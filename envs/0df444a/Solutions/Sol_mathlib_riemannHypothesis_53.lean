-- Prove2me | solution 53 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:12.970809+00:00
-- url     : https://prove2.me/submissions/be33bf0a-b762-4d5e-bdd7-c0a5020d4fff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_unit_height_signed_critical_band_certificates
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

-- Step 1: `MasulloRH.unit_height_signed_critical_band_certificates` implies `MasulloRH.cofinal_signed_critical_band_certificates` (accepted reduction of `MasulloRH.cofinal_signed_critical_band_certificates`).
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

-- Step 2: `MasulloRH.cofinal_signed_critical_band_certificates` implies `MasulloRH.finite_square_prime_energy_cap` (accepted reduction of `MasulloRH.finite_square_prime_energy_cap`).
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

-- Step 3: `MasulloRH.finite_square_prime_energy_cap` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  by
  obtain ⟨-, h2, -⟩ := MasulloRH.riemannHypothesis_iff_square_sampled_prime_energy
  exact h2.mpr (fun N => MasulloRH.finite_square_prime_energy_cap N)

end
