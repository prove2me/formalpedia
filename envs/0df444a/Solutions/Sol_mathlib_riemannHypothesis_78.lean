-- Prove2me | solution 78 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:46.869292+00:00
-- url     : https://prove2.me/submissions/244dc853-7e2c-46f6-ade4-2d647d76d550
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Mathlib.Data.Rat.Cast.Order
import Theorems.Thm_MasulloRH_unit_height_em_adaptive_ball_certificates
import Theorems.Thm_MasulloRH_unit_height_em_enclosure
import Theorems.Thm_MasulloRH_unit_height_zeta_right_rectangle_deriv_bound
import Mathlib.Data.Finset.Max
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_riemannZeta_conj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_MasulloRH_critical_zero_band_of_signed_brackets
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_verified_square_prime_energy_prefix
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e2_1e3
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e3_1e4
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e4_1e5
import Theorems.Thm_MasulloRH_riemannHypothesis_iff_square_sampled_prime_energy

-- Step 1: `MasulloRH.unit_height_em_adaptive_ball_certificates` implies `MasulloRH.unit_height_em_mesh_pointwise_certificates` (accepted reduction of `MasulloRH.unit_height_em_mesh_pointwise_certificates`).
section

open Set
set_option autoImplicit false

theorem MasulloRH.unit_height_em_mesh_pointwise_certificates (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    let M : ℚ := 16 * (100003 + n)
    ∃ m : ℕ, 0 < m ∧
      ∀ i j : Fin (m + 1), ∃ (K N : ℕ), 1 ≤ K ∧ 1 ≤ N ∧
        let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
          (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
        let s : ℂ :=
          ⟨left + (1 - left) * ((i.val : ℝ) / m),
            bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
        ((2 * M / m + err : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K s N‖ := by
  intro margin left bottom top M
  let R := Complex.reProdIm (Icc left 1) (Icc bottom top)
  let center (p : ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2 : ℝ)⟩
  let err (K N : ℕ) : ℚ :=
    ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
      (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
  obtain ⟨points, rad, hAtPoint, hCover⟩ := MasulloRH.unit_height_em_adaptive_ball_certificates n k
  have hM : 0 ≤ (M : ℝ) := by dsimp [M]; push_cast; positivity
  have hBot : 0 < bottom := by dsimp [bottom, margin]; positivity
  have hMargin : margin ≤ 1 / 3 := by
    dsimp [margin]
    exact one_div_le_one_div_of_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hLeft : left ≤ 1 := by dsimp [left]; linarith
  have hBottom : bottom ≤ top := by dsimp [bottom, top]; linarith
  have hRNonempty : R.Nonempty :=
    ⟨⟨left, bottom⟩, Complex.mem_reProdIm.mpr ⟨⟨le_rfl, hLeft⟩, ⟨le_rfl, hBottom⟩⟩⟩
  have hRCompact : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hRConv : Convex ℝ R := by
    change Convex ℝ ((Complex.reLm ⁻¹' Icc left 1) ∩ (Complex.imLm ⁻¹' Icc bottom top))
    exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
      ((convex_Icc _ _).linear_preimage Complex.imLm)
  have hDiff (s : ℂ) (hs : s ∈ R) : DifferentiableAt ℂ riemannZeta s := by
    apply differentiableAt_riemannZeta
    rintro rfl
    exact hBot.not_ge (by simpa only [Complex.one_im] using (Complex.mem_reProdIm.mp hs).2.1)
  have hD (s : ℂ) (hs : s ∈ R) : ‖deriv riemannZeta s‖ ≤ (M : ℝ) := by
    have h := MasulloRH.unit_height_zeta_right_rectangle_deriv_bound n k s hs
    dsimp [M]
    push_cast
    exact h
  have hEnc (s : ℂ) (hs : s ∈ R) (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
      ‖riemannZeta s - ZetaReflection.EMHigh.emFinite K s N‖ ≤ (err K N : ℝ) :=
    MasulloRH.unit_height_em_enclosure n k K N hK hN s hs
  have hNonzero (s : ℂ) (hs : s ∈ R) : riemannZeta s ≠ 0 := by
    obtain ⟨p, hp, hr⟩ := hCover s hs
    change dist s (center p) < (rad p : ℝ) at hr
    obtain ⟨hpR, K, N, hK, hN, hgap⟩ := hAtPoint p hp
    change center p ∈ R at hpR
    change ((M * rad p + err K N : ℚ) : ℝ) <
      ‖ZetaReflection.EMHigh.emFinite K (center p) N‖ at hgap
    push_cast at hgap
    have hder := hRConv.norm_image_sub_le_of_norm_deriv_le hDiff hD hs hpR
    rw [← dist_eq_norm (center p) s, dist_comm (center p) s] at hder
    have htri := norm_sub_norm_le (ZetaReflection.EMHigh.emFinite K (center p) N)
      (riemannZeta (center p))
    rw [norm_sub_rev] at htri
    have hval := hEnc (center p) hpR K N hK hN
    have hrad := mul_le_mul_of_nonneg_left hr.le hM
    intro hZero
    rw [hZero, sub_zero] at hder
    linarith
  obtain ⟨smin, hsmin, hMin⟩ := hRCompact.exists_isMinOn hRNonempty
    (show ContinuousOn riemannZeta R from
      (fun s hs => (hDiff s hs).continuousAt.continuousWithinAt)).norm
  let δ := ‖riemannZeta smin‖
  have hδ : 0 < δ := norm_pos_iff.mpr (hNonzero smin hsmin)

  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (4 * (M : ℝ) / δ))
  have hmReal : 0 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmPos : 0 < m := by exact_mod_cast hmReal
  let cost : ℚ := 2 * M / m
  have hCost : (cost : ℝ) < δ / 2 := by
    have h := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hm)
    dsimp [cost]
    push_cast
    exact (div_lt_iff₀ hmReal).2 (by nlinarith)
  let c : ℝ := ((100002 + n + 2 * 1 : ℕ) : ℝ) ^ 3 / 108
  have hCastErr (N : ℕ) : (err 1 N : ℝ) = c / (N : ℝ) ^ 2 := by
    dsimp only [err, c]
    push_cast
    norm_num
    rw [div_div]
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (4 * c / δ))
  have hNReal : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNPos : 1 ≤ N := by exact_mod_cast hNReal.le
  have hNLarge : 4 * c < (N : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hN)
  have hNSq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hNReal, sq_nonneg ((N : ℝ) - 1)]
  have hSmall : 2 * (err 1 N : ℝ) < δ / 2 := by
    have hAux : 4 * c < (N : ℝ) ^ 2 * δ :=
      hNLarge.trans_le (mul_le_mul_of_nonneg_right hNSq hδ.le)
    rw [hCastErr, ← mul_div_assoc]
    exact (div_lt_iff₀ (by positivity)).2 (by nlinarith)
  have hCoord {a b : ℝ} (hab : a ≤ b) (i : Fin (m + 1)) :
      a + (b - a) * ((i.val : ℝ) / m) ∈ Icc a b := by
    have hi : (i.val : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hq : (i.val : ℝ) / m ∈ Icc 0 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hmReal.le, (div_le_one hmReal).2 hi⟩
    have hlo := mul_nonneg (sub_nonneg.mpr hab) hq.1
    have hhi := mul_le_of_le_one_right (sub_nonneg.mpr hab) hq.2
    exact ⟨by linarith, by linarith⟩
  refine ⟨m, hmPos, ?_⟩
  intro i j
  let s : ℂ := ⟨left + (1 - left) * (i.val / (m : ℝ)),
    bottom + (top - bottom) * (j.val / (m : ℝ))⟩
  have hs : s ∈ R := Complex.mem_reProdIm.mpr ⟨hCoord hLeft i, hCoord hBottom j⟩
  refine ⟨1, N, le_rfl, hNPos, ?_⟩
  change ((cost + err 1 N : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite 1 s N‖
  push_cast
  have hBound := hEnc s hs 1 N le_rfl hNPos
  have hTri := norm_sub_norm_le (riemannZeta s) (ZetaReflection.EMHigh.emFinite 1 s N)
  have hLower : δ ≤ ‖riemannZeta s‖ := hMin hs
  linarith

end

-- Step 2: `MasulloRH.unit_height_em_mesh_pointwise_certificates` implies `MasulloRH.unit_height_em_mesh_certificates` (accepted reduction of `MasulloRH.unit_height_em_mesh_certificates`).
section

set_option autoImplicit false

open Set

theorem MasulloRH.unit_height_em_mesh_certificates (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    let M : ℚ := 16 * (100003 + n)
    ∃ (m K N : ℕ), 0 < m ∧ 1 ≤ K ∧ 1 ≤ N ∧
      let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
        (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
      ∀ i j : Fin (m + 1),
        let s : ℂ :=
          ⟨left + (1 - left) * ((i.val : ℝ) / m),
            bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
        ((2 * M / m + err : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K s N‖ := by
  intro margin left bottom top M
  obtain ⟨m, hm, hPointwise⟩ := MasulloRH.unit_height_em_mesh_pointwise_certificates n k
  let err (K N : ℕ) : ℚ :=
    ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
      (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
  let sample (i j : Fin (m + 1)) : ℂ :=
    ⟨left + (1 - left) * ((i.val : ℝ) / m),
      bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
  let cost : ℚ := 2 * M / m
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmargin : margin ≤ 1 / 3 := by
    dsimp [margin]
    exact one_div_le_one_div_of_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hLeft : left ≤ 1 := by dsimp [left]; linarith
  have hBottom : bottom ≤ top := by dsimp [bottom, top]; linarith
  have hCoord {a b : ℝ} (hab : a ≤ b) (i : Fin (m + 1)) :
      a + (b - a) * ((i.val : ℝ) / m) ∈ Icc a b := by
    have hi : (i.val : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hq : (i.val : ℝ) / m ∈ Icc 0 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hm'.le, (div_le_one hm').2 hi⟩
    have hlo := mul_nonneg (sub_nonneg.mpr hab) hq.1
    have hhi := mul_le_of_le_one_right (sub_nonneg.mpr hab) hq.2
    exact ⟨by linarith, by linarith⟩
  have hIn (i j : Fin (m + 1)) :
      sample i j ∈ Complex.reProdIm (Icc left 1) (Icc bottom top) :=
    Complex.mem_reProdIm.mpr ⟨hCoord hLeft i, hCoord hBottom j⟩
  have hEncl (i j : Fin (m + 1)) (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
      ‖riemannZeta (sample i j) - ZetaReflection.EMHigh.emFinite K (sample i j) N‖ ≤
        (err K N : ℝ) :=
    MasulloRH.unit_height_em_enclosure n k K N hK hN _ (hIn i j)

  -- Transfer each pointwise certificate to a strict, precision-independent margin.
  have hMargin (i j : Fin (m + 1)) : (cost : ℝ) < ‖riemannZeta (sample i j)‖ := by
    obtain ⟨K, N, hK, hN, hGap⟩ := hPointwise i j
    change ((cost + err K N : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K (sample i j) N‖ at hGap
    push_cast at hGap
    have hError := hEncl i j K N hK hN
    have hTriangle := norm_sub_norm_le (ZetaReflection.EMHigh.emFinite K (sample i j) N)
      (riemannZeta (sample i j))
    rw [norm_sub_rev] at hTriangle
    linarith

  let gap (p : Fin (m + 1) × Fin (m + 1)) : ℝ :=
    ‖riemannZeta (sample p.1 p.2)‖ - (cost : ℝ)
  obtain ⟨p, _, hp⟩ := Finset.exists_min_image Finset.univ gap Finset.univ_nonempty
  let δ := gap p
  have hδ : 0 < δ := sub_pos.mpr (hMargin p.1 p.2)
  have hMin (i j : Fin (m + 1)) :
      δ ≤ ‖riemannZeta (sample i j)‖ - (cost : ℝ) :=
    hp (i, j) (Finset.mem_univ _)

  -- At first order the enclosure radius is c / N², uniformly over the mesh.
  let c : ℝ := ((100002 + n + 2 * 1 : ℕ) : ℝ) ^ 3 / 108
  have hCastErr (N : ℕ) : (err 1 N : ℝ) = c / (N : ℝ) ^ 2 := by
    dsimp only [err, c]
    push_cast
    norm_num
    rw [div_div]
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * c / δ))
  have hNReal : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNPos : 1 ≤ N := by exact_mod_cast hNReal.le
  have hNLarge : 2 * c < (N : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hN)
  have hNSq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hNReal, sq_nonneg ((N : ℝ) - 1)]
  have hSmall : 2 * (err 1 N : ℝ) < δ := by
    rw [hCastErr, ← mul_div_assoc]
    exact (div_lt_iff₀ (by positivity)).2
      (hNLarge.trans_le (mul_comm (N : ℝ) δ ▸
        mul_le_mul_of_nonneg_left hNSq hδ.le))

  refine ⟨m, 1, N, hm, le_rfl, hNPos, ?_⟩
  change ∀ i j : Fin (m + 1),
    ((cost + err 1 N : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite 1 (sample i j) N‖
  intro i j
  push_cast
  have hError := hEncl i j 1 N le_rfl hNPos
  have hTriangle := norm_sub_norm_le (riemannZeta (sample i j))
    (ZetaReflection.EMHigh.emFinite 1 (sample i j) N)
  linarith [hMin i j]

end

-- Step 3: `MasulloRH.unit_height_em_mesh_certificates` implies `MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates` (accepted reduction of `MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates`).
section

set_option autoImplicit false

theorem MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    ∃ (m : ℕ) (M : ℚ), 0 < m ∧ 0 ≤ M ∧
      (∀ s ∈ Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top),
        ‖deriv riemannZeta s‖ ≤ (M : ℝ)) ∧
      ∀ i j : Fin (m + 1),
        let s : ℂ :=
          ⟨left + (1 - left) * ((i.val : ℝ) / m),
            bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
        2 * (M : ℝ) / m < ‖riemannZeta s‖ := by
  intro margin left bottom top
  obtain ⟨m, K, N, hm, hK, hN, hmesh⟩ := MasulloRH.unit_height_em_mesh_certificates n k
  let M : ℚ := 16 * (100003 + n)
  refine ⟨m, M, hm, ?_, ?_, ?_⟩
  · dsimp [M]
    positivity
  · intro s hs
    have hderiv := MasulloRH.unit_height_zeta_right_rectangle_deriv_bound n k s hs
    have hM_cast : (M : ℝ) = (16 : ℝ) * (100003 + n) := by
      dsimp [M]
      push_cast
      ring
    rw [hM_cast]
    exact hderiv
  · intro i j
    dsimp only
    set s : ℂ :=
      ⟨left + (1 - left) * ((i.val : ℝ) / m),
        bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hmargin_pos : 0 < margin := by
      dsimp [margin]
      positivity
    have hmargin_le : margin ≤ 1 / 3 := by
      dsimp [margin]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hleft_le_one : left ≤ 1 := by
      dsimp [left]
      linarith
    have hbottom_le_top : bottom ≤ top := by
      dsimp [bottom, top]
      linarith
    have hi_nonneg : 0 ≤ (i.val : ℝ) / (m : ℝ) := by positivity
    have hi_le_one : (i.val : ℝ) / (m : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hm_pos, one_mul]
      exact Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt)
    have hj_nonneg : 0 ≤ (j.val : ℝ) / (m : ℝ) := by positivity
    have hj_le_one : (j.val : ℝ) / (m : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hm_pos, one_mul]
      exact Nat.cast_le.mpr (Nat.le_of_lt_succ j.isLt)
    have hs_mem : s ∈ Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top) := by
      refine Complex.mem_reProdIm.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · change left ≤ left + (1 - left) * ((i.val : ℝ) / m)
        have : 0 ≤ (1 - left) * ((i.val : ℝ) / m) :=
          mul_nonneg (sub_nonneg.mpr hleft_le_one) hi_nonneg
        linarith
      · change left + (1 - left) * ((i.val : ℝ) / m) ≤ 1
        have : (1 - left) * ((i.val : ℝ) / m) ≤ (1 - left) * 1 :=
          mul_le_mul_of_nonneg_left hi_le_one (sub_nonneg.mpr hleft_le_one)
        linarith
      · change bottom ≤ bottom + (top - bottom) * ((j.val : ℝ) / m)
        have : 0 ≤ (top - bottom) * ((j.val : ℝ) / m) :=
          mul_nonneg (sub_nonneg.mpr hbottom_le_top) hj_nonneg
        linarith
      · change bottom + (top - bottom) * ((j.val : ℝ) / m) ≤ top
        have : (top - bottom) * ((j.val : ℝ) / m) ≤ (top - bottom) * 1 :=
          mul_le_mul_of_nonneg_left hj_le_one (sub_nonneg.mpr hbottom_le_top)
        linarith
    let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
      (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
    have henc :
        ‖riemannZeta s - ZetaReflection.EMHigh.emFinite K s N‖ ≤ (err : ℝ) :=
      MasulloRH.unit_height_em_enclosure n k K N hK hN s hs_mem
    have hpt :
        ((2 * M / m + err : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K s N‖ :=
      hmesh i j
    have htri :
        ‖ZetaReflection.EMHigh.emFinite K s N‖ ≤
          ‖riemannZeta s‖ + ‖riemannZeta s - ZetaReflection.EMHigh.emFinite K s N‖ := by
      have h0 := norm_sub_le (riemannZeta s) (riemannZeta s - ZetaReflection.EMHigh.emFinite K s N)
      have hsub : riemannZeta s - (riemannZeta s - ZetaReflection.EMHigh.emFinite K s N) =
          ZetaReflection.EMHigh.emFinite K s N := by ring
      rwa [hsub] at h0
    have hcast : ((2 * M / m + err : ℚ) : ℝ) = 2 * (M : ℝ) / (m : ℝ) + (err : ℝ) := by
      push_cast
      ring
    linarith

end

-- Step 4: `MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates` implies `MasulloRH.unit_height_signed_critical_band_certificates` (accepted reduction of `MasulloRH.unit_height_signed_critical_band_certificates`).
section

open MasulloRH
open scoped ComplexConjugate

set_option autoImplicit false

private theorem exists_subdivision_point {a b x : ℝ} {m : ℕ}
    (hm : 0 < m) (hab : a < b) (hwidth : b - a ≤ 1) (hx : x ∈ Set.Icc a b) :
    ∃ i : Fin (m + 1),
      let y := a + (b - a) * ((i.val : ℝ) / m)
      y ∈ Set.Icc a b ∧ |x - y| ≤ 1 / (m : ℝ) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hw : 0 < b - a := sub_pos.mpr hab
  let t := (x - a) * (m : ℝ) / (b - a)
  have ht : 0 ≤ t := div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) hm'.le) hw.le
  have htm : t ≤ (m : ℝ) := (div_le_iff₀ hw).mpr (by
    rw [mul_comm (m : ℝ)]
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right hx.2 a) hm'.le)
  let i := ⌊t⌋₊
  have hit : (i : ℝ) ≤ t := Nat.floor_le ht
  have hti : t ≤ (i : ℝ) + 1 := (Nat.lt_floor_add_one t).le
  have him : i ≤ m := by exact_mod_cast hit.trans htm
  refine ⟨⟨i, Nat.lt_succ_of_le him⟩, ?_⟩
  let y := a + (b - a) * ((i : ℝ) / m)
  have hstep : x - y = (b - a) * (t - (i : ℝ)) / m := by
    dsimp [y, t]
    field_simp [hw.ne', hm'.ne']
    ring
  have hyx : 0 ≤ x - y := by
    rw [hstep]
    exact div_nonneg (mul_nonneg hw.le (sub_nonneg.mpr hit)) hm'.le
  change y ∈ Set.Icc a b ∧ |x - y| ≤ _
  refine ⟨⟨le_add_of_nonneg_right (mul_nonneg hw.le (div_nonneg (Nat.cast_nonneg i) hm'.le)),
    (sub_nonneg.mp hyx).trans hx.2⟩, ?_⟩
  rw [abs_of_nonneg hyx, hstep]
  have hunit : t - (i : ℝ) ≤ 1 := by linarith only [hti]
  exact div_le_div_of_nonneg_right
    (by simpa using mul_le_mul hwidth hunit (sub_nonneg.mpr hit) zero_le_one) hm'.le

private theorem no_zero_right_of_line (n : ℕ) (s : ℂ)
    (hs : 1 / 2 < s.re) (hs₁ : s.re ≤ 1)
    (hL : (100000 : ℝ) + n < s.im) (hH : s.im ≤ (100000 : ℝ) + n + 1) :
    riemannZeta s ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt
    (lt_min (sub_pos.mpr hs) (sub_pos.mpr hL) :
      0 < min (s.re - 1 / 2) (s.im - ((100000 : ℝ) + n)))
  let margin : ℝ := 1 / ((k : ℝ) + 3)
  let left : ℝ := 1 / 2 + margin
  let bottom : ℝ := (100000 : ℝ) + n + margin
  let top : ℝ := (100000 : ℝ) + n + 1
  have hmargin : 0 < margin := by dsimp [margin]; positivity
  have hsmall : margin ≤ 1 / 3 := by
    dsimp [margin]
    exact one_div_le_one_div_of_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hclose : margin ≤ 1 / ((k : ℝ) + 1) := by
    dsimp [margin]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hleft : left < 1 := by dsimp [left]; linarith
  have hbottom : bottom < top := by dsimp [bottom, top]; linarith
  have hwre : 1 - left ≤ 1 := by dsimp [left]; linarith
  have hwim : top - bottom ≤ 1 := by dsimp [top, bottom]; linarith
  have hsre : s.re ∈ Set.Icc left 1 :=
    ⟨by dsimp [left]; linarith [(hclose.trans_lt hk).trans_le (min_le_left _ _)], hs₁⟩
  have hsim : s.im ∈ Set.Icc bottom top :=
    ⟨by dsimp [bottom]; linarith [(hclose.trans_lt hk).trans_le (min_le_right _ _)], hH⟩
  obtain ⟨m, M, hm, hM, hderiv, hsamples⟩ := unit_height_zeta_right_rectangle_mesh_certificates n k
  obtain ⟨i, hi, hdist_re⟩ := exists_subdivision_point hm hleft hwre hsre
  obtain ⟨j, hj, hdist_im⟩ := exists_subdivision_point hm hbottom hwim hsim
  let q : ℂ := ⟨left + (1 - left) * ((i.val : ℝ) / m),
    bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
  let R := Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top)
  have hsR : s ∈ R := Complex.mem_reProdIm.mpr ⟨hsre, hsim⟩
  have hqR : q ∈ R := Complex.mem_reProdIm.mpr ⟨hi, hj⟩
  have hconvex : Convex ℝ R := by
    change Convex ℝ ((Complex.reLm ⁻¹' Set.Icc left 1) ∩
      (Complex.imLm ⁻¹' Set.Icc bottom top))
    have hre : Convex ℝ (Set.Icc left 1) := convex_Icc _ _
    have him : Convex ℝ (Set.Icc bottom top) := convex_Icc _ _
    exact (hre.linear_preimage Complex.reLm).inter (him.linear_preimage Complex.imLm)
  have hdiff (z : ℂ) (hz : z ∈ R) : DifferentiableAt ℂ riemannZeta z := by
    apply differentiableAt_riemannZeta
    intro hz₁
    have hpos : 0 < bottom := by dsimp [bottom]; positivity
    have him := (Complex.mem_reProdIm.mp hz).2.1
    rw [hz₁, Complex.one_im] at him
    exact (not_le_of_gt hpos) him
  have hdist : ‖q - s‖ ≤ 2 / (m : ℝ) := by
    calc
      ‖q - s‖ ≤ |q.re - s.re| + |q.im - s.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |s.re - q.re| + |s.im - q.im| := by rw [abs_sub_comm q.re, abs_sub_comm q.im]
      _ ≤ 1 / (m : ℝ) + 1 / (m : ℝ) := add_le_add hdist_re hdist_im
      _ = 2 / (m : ℝ) := by ring
  intro hz
  have hval := hconvex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv hsR hqR
  rw [hz, sub_zero] at hval
  have hM' : 0 ≤ (M : ℝ) := by exact_mod_cast hM
  have hbound := hval.trans (mul_le_mul_of_nonneg_left hdist hM')
  have hsample : 2 * (M : ℝ) / (m : ℝ) < ‖riemannZeta q‖ := hsamples i j
  rw [← mul_div_assoc, mul_comm (M : ℝ)] at hbound
  exact (not_lt_of_ge hbound) hsample

private theorem zero_on_line_in_band (n : ℕ) (z : ZetaZerosInTraceStrip (1 / 2))
    (hz : (100000 : ℝ) + n < z.val.im ∧ z.val.im ≤ (100000 : ℝ) + n + 1) :
    z.val.re = 1 / 2 := by
  apply le_antisymm
  · exact le_of_not_gt fun h =>
      no_zero_right_of_line n z.val h z.prop.2.2.1.le hz.1 hz.2 z.prop.1
  · apply le_of_not_gt
    intro h
    let w : ℂ := 1 - conj z.val
    have hwre : w.re = 1 - z.val.re := by simp [w]
    have hwim : w.im = z.val.im := by simp [w]
    have hnontrivial (j : ℕ) : conj z.val ≠ -(j : ℂ) := by
      intro hj
      have hr := congrArg Complex.re hj
      simp only [Complex.conj_re, Complex.neg_re, Complex.natCast_re] at hr
      linarith only [hr, z.prop.2.1, Nat.cast_nonneg (α := ℝ) j]
    have hpole : conj z.val ≠ 1 := by
      intro h₁
      have hr := congrArg Complex.re h₁
      simp only [Complex.conj_re, Complex.one_re] at hr
      linarith only [hr, z.prop.2.2.1]
    have hzero : riemannZeta w = 0 := by
      dsimp [w]
      rw [riemannZeta_one_sub hnontrivial hpole, riemannZeta_conj, z.prop.1, map_zero, mul_zero]
    exact no_zero_right_of_line n w (by linarith only [hwre, h])
      (by linarith only [hwre, z.prop.2.1]) (hwim.symm ▸ hz.1) (hwim.symm ▸ hz.2) hzero

private theorem finite_zeros_in_band (L H : ℝ) :
    {z : ZetaZerosInTraceStrip (1 / 2) | L < z.val.im ∧ z.val.im ≤ H}.Finite := by
  let R := Complex.reProdIm (Set.Icc (0 : ℝ) 1) (Set.Icc L H)
  have hR : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  refine (hR.inter_riemannZetaZeros_finite.preimage Subtype.val_injective.injOn).subset ?_
  intro z hz
  exact ⟨Complex.mem_reProdIm.mpr ⟨⟨z.prop.2.1.le, z.prop.2.2.1.le⟩, ⟨hz.1.le, hz.2⟩⟩,
    mem_riemannZetaZeros.mpr z.prop.1⟩

theorem MasulloRH.unit_height_signed_critical_band_certificates (n : ℕ) :
    ∃ (E : Finset (ZetaZerosInTraceStrip (1/2))) (B : Finset (ℚ×ℚ)),
      (∀ z ∈ E, (100000:ℝ)+n < z.val.im ∧ z.val.im ≤ (100000:ℝ)+n+1 ∧ z.val.re=1/2) ∧
      (∀ i ∈ B, (100000:ℝ)+n ≤ (i.1:ℝ) ∧ i.1 < i.2 ∧ (i.2:ℝ) ≤ (100000:ℝ)+n+1 ∧
        (completedRiemannZeta (1/2+(i.1:ℂ)*Complex.I)).re *
        (completedRiemannZeta (1/2+(i.2:ℂ)*Complex.I)).re < 0) ∧
      (∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (Set.Ioo (i.1:ℝ) (i.2:ℝ)) (Set.Ioo (j.1:ℝ) (j.2:ℝ))) ∧
      (∀ z ∈ E, ∀ i ∈ B, z.val.im ∉ Set.Ioo (i.1:ℝ) (i.2:ℝ)) ∧
      Set.encard {z : ZetaZerosInTraceStrip (1/2) |
        (100000:ℝ)+n<z.val.im ∧ z.val.im ≤ (100000:ℝ)+n+1} ≤
          ((E.card+B.card+1:ℕ):ℕ∞) := by
  classical
  let Z : Set (ZetaZerosInTraceStrip (1 / 2)) :=
    {z | (100000 : ℝ) + n < z.val.im ∧ z.val.im ≤ (100000 : ℝ) + n + 1}
  have hfinite : Z.Finite := finite_zeros_in_band _ _
  let E := hfinite.toFinset
  refine ⟨E, ∅, ?_, by simp, by simp, by simp, ?_⟩
  · intro z hz
    have hzZ : z ∈ Z := hfinite.mem_toFinset.mp hz
    exact ⟨hzZ.1, hzZ.2, zero_on_line_in_band n z hzZ⟩
  · rw [hfinite.encard_eq_coe_toFinset_card]
    simp only [Finset.card_empty, Nat.add_zero]
    exact_mod_cast Nat.le_succ E.card

end

-- Step 5: `MasulloRH.unit_height_signed_critical_band_certificates` implies `MasulloRH.cofinal_signed_critical_band_certificates` (accepted reduction of `MasulloRH.cofinal_signed_critical_band_certificates`).
section

open MasulloRH Set Finset Filter Topology

private theorem multiplicity_pos (ρ : ZetaZerosInTraceStrip (1/2)) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.one_re] at hr
    linarith [ρ.prop.2.2.1]
  have hA := analyticOn_riemannZeta
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfin := hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  apply Nat.pos_of_ne_zero
  unfold analyticOrderNatAt
  exact fun h => (ENat.toNat_eq_zero.mp h).elim
    ((hA _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1) hfin

private theorem finite_zeros_to_height (H : ℝ) (hH : 0 ≤ H) :
    {z : ZetaZerosInTraceStrip (1/2) | |z.val.im| ≤ H}.Finite := by
  let w := zeroDecayWeight (1/2)
  have hlim : Tendsto w cofinite (𝓝 0) := (weighted_zero_summability (1/2) (by norm_num)).tendsto_cofinite_zero
  have he := hlim.eventually (gt_mem_nhds (show (0:ℝ) < 1/(1+H^2) by positivity))
  have hbad : {z | ¬ w z < 1/(1+H^2)}.Finite := by
    simpa only [eventually_cofinite] using he
  apply hbad.subset
  intro z hz
  change |z.val.im| ≤ H at hz
  change ¬w z < 1/(1+H^2)
  apply not_lt.mpr
  have hysq : z.val.im^2 ≤ H^2 := by nlinarith [sq_abs z.val.im,mul_self_le_mul_self (abs_nonneg _) hz]
  have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta z.val := by exact_mod_cast multiplicity_pos z
  exact (one_div_le_one_div_of_le (by positivity) (by linarith only [hysq])).trans
    (div_le_div_of_nonneg_right hm (by positivity))

private theorem positive_band_zero_on_line (z : ZetaZerosInTraceStrip (1/2))
    (hz : 100000 < z.val.im) : z.val.re = 1/2 := by
  let d : ℝ := z.val.im-100000
  have hd : 0 < d := by dsimp [d]; linarith
  let n : ℕ := Nat.ceil d - 1
  have hn : 1 ≤ Nat.ceil d := Nat.one_le_ceil_iff.mpr hd
  have hnlower : (n:ℝ) < d := Nat.add_one_le_ceil_iff.mp (by dsimp [n]; omega)
  have hncast : (n:ℝ)+1 = (Nat.ceil d : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hn : (Nat.ceil d-1)+1=Nat.ceil d)
  have hnupper : d ≤ (n:ℝ)+1 := by rw [hncast]; exact Nat.le_ceil d
  obtain ⟨E,B,hE,hB,hD,hED,hcount⟩ := unit_height_signed_critical_band_certificates n
  have h := critical_zero_band_of_signed_brackets ((100000:ℝ)+n) ((100000:ℝ)+n+1)
    E B hE hB hD hED hcount
  apply h z
  · rw [abs_of_pos (by linarith : 0 < z.val.im)]
    dsimp [d] at hnlower
    linarith
  · rw [abs_of_pos (by linarith : 0 < z.val.im)]
    dsimp [d] at hnupper
    linarith

open Set Finset

theorem MasulloRH.cofinal_signed_critical_band_certificates (T : ℕ) :
    ∃ H : ℕ, T ≤ H ∧ ∃ (E : Finset (ZetaZerosInTraceStrip (1/2))) (B : Finset (ℚ×ℚ)),
      (∀ z ∈ E, 100000 < z.val.im ∧ z.val.im ≤ (H:ℝ) ∧ z.val.re=1/2) ∧
      (∀ i ∈ B, 100000 ≤ (i.1:ℝ) ∧ i.1 < i.2 ∧ (i.2:ℝ) ≤ H ∧
        (completedRiemannZeta (1/2+(i.1:ℂ)*Complex.I)).re * (completedRiemannZeta (1/2+(i.2:ℂ)*Complex.I)).re < 0) ∧
      (∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (Set.Ioo (i.1:ℝ) (i.2:ℝ)) (Set.Ioo (j.1:ℝ) (j.2:ℝ))) ∧
      (∀ z ∈ E, ∀ i ∈ B, z.val.im ∉ Set.Ioo (i.1:ℝ) (i.2:ℝ)) ∧
      Set.encard {z : ZetaZerosInTraceStrip (1/2) | 100000<z.val.im ∧ z.val.im ≤ H} ≤ ((E.card+B.card+1:ℕ):ℕ∞)  := by
  classical
  let H : ℕ := max T 100000
  let Z : Set (ZetaZerosInTraceStrip (1/2)) :=
    {z | 100000 < z.val.im ∧ z.val.im ≤ (H:ℝ)}
  have hfin : Z.Finite := (finite_zeros_to_height (H:ℝ) (Nat.cast_nonneg H)).subset (by
    intro z hz
    change 100000 < z.val.im ∧ z.val.im ≤ (H:ℝ) at hz
    change |z.val.im| ≤ (H:ℝ)
    rw [abs_of_pos (by linarith [hz.1] : 0 < z.val.im)]
    exact hz.2)
  let E := hfin.toFinset
  refine ⟨H, le_max_left _ _, E, ∅, ?_, by simp, by simp, by simp, ?_⟩
  · intro z hz
    have h : z ∈ Z := (hfin.mem_toFinset).mp hz
    exact ⟨h.1, h.2, positive_band_zero_on_line z h.1⟩
  · change Set.encard Z ≤ ((E.card + (∅ : Finset (ℚ×ℚ)).card + 1 : ℕ):ℕ∞)
    rw [hfin.encard_eq_coe_toFinset_card]
    simp only [Finset.card_empty, Nat.add_zero]
    exact_mod_cast (Nat.le_succ E.card)

end

-- Step 6: `MasulloRH.cofinal_signed_critical_band_certificates` implies `MasulloRH.finite_square_prime_energy_cap` (accepted reduction of `MasulloRH.finite_square_prime_energy_cap`).
section

open MasulloRH Set Finset ArithmeticFunction MeasureTheory
private theorem critical_to_100000 (z : ZetaZerosInTraceStrip (1/2)) (hz : |z.val.im| ≤ 100000) :
    z.val.re = 1/2 := by
  have hpos (s : ℂ) (hs : riemannZeta s=0) (h0 : 0 < s.re) (h1 : s.re < 1)
      (him : 0 ≤ s.im) (hhigh : s.im ≤ 100000) : s.re=1/2 := by
    by_cases h2 : s.im ≤ 2
    · exact (ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six h0 h1
        (by rw [abs_of_nonneg him]; linarith) hs).elim
    by_cases h14 : s.im ≤ 14
    · exact (TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen s h0 h1 (by linarith) h14 hs).elim
    by_cases h100 : s.im ≤ 100
    · exact TaoFivePrimes.rh_verified_block_14_1e2 s hs h0 h1 (by linarith) (by norm_num; exact h100)
    by_cases h1k : s.im ≤ 1000
    · exact TaoFivePrimes.rh_verified_block_1e2_1e3 s hs h0 h1 (by norm_num; linarith) (by norm_num; exact h1k)
    by_cases h10k : s.im ≤ 10000
    · exact TaoFivePrimes.rh_verified_block_1e3_1e4 s hs h0 h1 (by norm_num; linarith) (by norm_num; exact h10k)
    exact TaoFivePrimes.rh_verified_block_1e4_1e5 s hs h0 h1 (by norm_num; linarith) (by norm_num; exact hhigh)
  by_cases hr : 0 ≤ z.val.im
  · exact hpos z.val z.prop.1 z.prop.2.1 z.prop.2.2.1 hr ((le_abs_self _).trans hz)
  have hnot (j : ℕ) : z.val ≠ -j := by
    intro he; have h := congrArg Complex.re he; simp only [Complex.neg_re,Complex.natCast_re] at h
    linarith [z.prop.2.1,j.cast_nonneg (α:=ℝ)]
  have hnot1 : z.val ≠ 1 := by
    intro he; have h := congrArg Complex.re he; rw [Complex.one_re] at h; linarith [z.prop.2.2.1]
  have hzero : riemannZeta (1-z.val)=0 := by rw [riemannZeta_one_sub hnot hnot1,z.prop.1,mul_zero]
  have h := hpos (1-z.val) hzero (by simp; linarith [z.prop.2.2.1])
    (by simp; linarith [z.prop.2.1]) (by simp; linarith) (by simp; linarith [neg_le_abs z.val.im])
  simp at h
  linarith


private theorem height_budget (x : ℝ) (hx : 100 ≤ x) :
    2*(10+Real.log (x^4))*(x-97) ≤ 5/2+2*x^4-1 := by
  have hx0 : 0 < x := by linarith
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hlog := Real.log_le_sub_one_of_pos hx0
  have h1 : 2*(10+4*Real.log x)*(x-97) ≤ (12+8*x)*(x-97) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : (12+8*x)*(x-97) ≤ (12+8*x)*x :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 := mul_nonneg (sq_nonneg x) (by nlinarith : 0 ≤ 2*x^2-10)
  nlinarith

open Finset ArithmeticFunction MeasureTheory Set

theorem MasulloRH.finite_square_prime_energy_cap (N : ℕ) :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    (∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)) ≤ 81  := by
  let M : ℕ := (N+100)^4
  obtain ⟨H, hH, E, B, hE, hB, hD, hED, hcount⟩ :=
    cofinal_signed_critical_band_certificates (3+2*M)
  have hband := critical_zero_band_of_signed_brackets 100000 (H:ℝ) E B hE hB hD hED hcount
  have hcover (z : ZetaZerosInTraceStrip (1/2))
      (hz : |z.val.im| ≤ 5/2+2*(M:ℝ)) : z.val.re ≤ 1/2 := by
    by_cases hsmall : |z.val.im| ≤ 100000
    · exact (critical_to_100000 z hsmall).le
    · have hH' : (3:ℝ)+2*(M:ℝ) ≤ H := by exact_mod_cast hH
      exact (hband z (lt_of_not_ge hsmall) (by linarith)).le
  have hM : 1 ≤ M := by
    have hpos : 0 < M := by dsimp [M]; positivity
    omega
  have hbudget : 2*(10+Real.log M)*((N:ℝ)+3) ≤ 5/2+2*(M:ℝ)-1 := by
    have h := height_budget ((N:ℝ)+100) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
    simpa only [M, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat,
      show (N:ℝ)+100-97 = (N:ℝ)+3 by ring] using h
  have h := verified_square_prime_energy_prefix.2.2 M N hM hcover hbudget
  exact h.trans (by norm_num)

end

-- Step 7: `MasulloRH.finite_square_prime_energy_cap` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  by
  obtain ⟨-, h2, -⟩ := MasulloRH.riemannHypothesis_iff_square_sampled_prime_energy
  exact h2.mpr (fun N => MasulloRH.finite_square_prime_energy_cap N)

end
