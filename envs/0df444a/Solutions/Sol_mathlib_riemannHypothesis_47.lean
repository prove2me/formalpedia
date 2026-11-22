-- Prove2me | solution 47 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:06.081851+00:00
-- url     : https://prove2.me/submissions/33069606-c542-4c47-8694-e7676933d526
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_NymanBeurling_real_certificate_has_rational_rounding
import Theorems.Thm_NymanBeurling_damped_moebius_finite_prefix_limit
import Theorems.Thm_NymanBeurling_damped_moebius_bounded_mean_square
import Theorems.Thm_NymanBeurling_finite_remainder_zero_obstruction
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

-- Step 1: `NymanBeurling.damped_moebius_bounded_mean_square` implies `NymanBeurling.arbitrarily_small_remainder_certificates` (accepted reduction of `NymanBeurling.arbitrarily_small_remainder_certificates`).
section

open Set Filter Topology Finset
noncomputable section
private abbrev H := lp (fun _ : ℕ => ℝ) 2

private theorem inner_limit (a : ℕ → H) (C : ℝ) (hb : ∀ n, ‖a n‖ ≤ C)
    (ht : ∀ i, Tendsto (fun j => a j i) atTop (𝓝 0)) (y : H) :
    Tendsto (fun n => inner ℝ y (a n)) atTop (𝓝 0) := by
  let S (N : ℕ) := ∑ i ∈ range N, lp.single 2 i (y i) (E := fun _ : ℕ => ℝ)
  have hs : Tendsto S atTop (𝓝 y) := (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ⊤) y).tendsto_sum_nat
  refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
  have hC : 0 < C+1 := by linarith [norm_nonneg (a 0),hb 0]
  obtain ⟨N,hN⟩ := (Metric.tendsto_nhds.mp hs (δ/(2*(C+1))) (by positivity)).exists
  have hpart : Tendsto (fun j => inner ℝ (S N) (a j)) atTop (𝓝 0) := by
    have he (i : ℕ) : Tendsto (fun j => inner ℝ (lp.single 2 i (y i) (E := fun _ : ℕ => ℝ)) (a j)) atTop (𝓝 0) := by
      simpa [lp.inner_single_left,real_inner_comm,Real.inner_apply,mul_comm] using (ht i).const_mul (y i)
    simpa only [S,sum_inner,sum_const_zero] using tendsto_finsetSum (range N) (fun i _ => he i)
  filter_upwards [Metric.tendsto_nhds.mp hpart (δ/2) (by positivity)] with j hj
  rw [dist_zero_right] at hj ⊢
  have hdiff : ‖y-S N‖*(C+1)<δ/2 := by
    rw [dist_comm,dist_eq_norm,lt_div_iff₀ (by positivity : 0<2*(C+1))] at hN
    linarith
  have herr : ‖inner ℝ (y-S N) (a j)‖ < δ/2 := (norm_inner_le_norm (𝕜 := ℝ) _ _).trans_lt
    ((mul_le_mul_of_nonneg_left (by linarith [hb j] : ‖a j‖≤C+1) (norm_nonneg _)).trans_lt hdiff)
  rw [show y=(y-S N)+S N by abel,inner_add_left]
  exact (norm_add_le _ _).trans_lt (by linarith)

private theorem closed_span (K : Submodule ℝ H) (v : H) (a : ℕ → H)
    (ha : ∀ j, v-a j ∈ K) (C : ℝ) (hb : ∀ j, ‖a j‖ ≤ C)
    (ht : ∀ i, Tendsto (fun j => a j i) atTop (𝓝 0)) : v ∈ K.topologicalClosure := by
  rw [←K.orthogonal_orthogonal_eq_closure,Kᗮ.mem_orthogonal]
  intro y hy
  have he (j : ℕ) : inner ℝ y (a j) = inner ℝ y v := by
    have h := ((K.mem_orthogonal' y).mp hy) _ (ha j)
    rwa [inner_sub_right,sub_eq_zero,eq_comm] at h
  exact tendsto_nhds_unique (tendsto_const_nhds (x := inner ℝ y v))
    ((inner_limit a C hb ht y).congr he)

private def den (n : ℕ) : ℝ := (n+1:ℝ)*(n+2:ℝ)
private def scale (n : ℕ) : ℝ := Real.sqrt (1/den n)
private theorem den_pos (n : ℕ) : 0 < den n := by dsimp [den]; positivity
private theorem scale_sq (n : ℕ) : scale n ^ 2 = 1/den n := Real.sq_sqrt (by positivity [den_pos n])
private def unitVector : H := ⟨scale,by
  apply memℓp_gen
  have hs : Summable (fun n : ℕ => 1/(n+1:ℝ)^2) := by
    simpa using (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ)/(n:ℝ)^2) 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by decide : 1<2))
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro n
  have se : ‖scale n‖ ^ (2:ENNReal).toReal = 1/den n := by norm_num [Real.norm_eq_abs,scale_sq]
  rw [se]
  apply one_div_le_one_div_of_le (by positivity)
  dsimp [den]; nlinarith⟩
private def remD (d n : ℕ) : ℝ := (((n+1)%d : ℕ):ℝ)/(d:ℝ)
private theorem rem_nonneg (d n : ℕ) : 0 ≤ remD d n := by dsimp [remD]; positivity
private theorem rem_le (d n : ℕ) : remD d n ≤ 1 := by
  rcases Nat.eq_zero_or_pos d with rfl|hp
  · simp [remD]
  · apply (div_le_one (by exact_mod_cast hp : (0:ℝ)<d)).mpr
    exact_mod_cast (Nat.mod_lt (n+1) hp).le
private def mode (d : ℕ) : H := ⟨fun n => remD d n * scale n,by
  apply unitVector.property.mono
  intro n
  change ‖remD d n * scale n‖ ≤ scale n
  have hn : 0 ≤ scale n := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (rem_nonneg _ _) hn)]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (rem_le _ _)⟩
private def V := Submodule.span ℝ (Set.range fun k : ℕ => mode (k+2))
private theorem mode_mem (d : ℕ) : mode d ∈ V := by
  match d with
  | 0 =>
    have he : mode 0 = (0:H) := by ext n; simp [mode,remD]
    rw [he];exact V.zero_mem
  | 1 =>
    have he : mode 1 = (0:H) := by
      ext n
      simp [mode,remD]
      exact Or.inl (Nat.mod_one n)
    rw [he];exact V.zero_mem
  | k+2 => exact Submodule.subset_span ⟨k,rfl⟩

private def coef (ε : ℝ) (d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^ε
private def R (ε : ℝ) (N n : ℕ) : ℝ :=
  1+∑ d ∈ Ioc 0 N, coef ε d*(((n+1)%d:ℕ):ℝ)/(d:ℝ)
private def resVec (ε : ℝ) (N : ℕ) : H := unitVector + ∑ d ∈ Ioc 0 N, coef ε d • mode d
private theorem rv_coord (ε : ℝ) (N n : ℕ) : resVec ε N n = R ε N n*scale n := by
  let ev := lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n
  change ev (unitVector + ∑ d ∈ Ioc 0 N, coef ε d • mode d) = _
  rw [map_add,map_sum]
  simp only [map_smul,smul_eq_mul]
  change scale n + ∑ d ∈ Ioc 0 N, coef ε d * (remD d n * scale n) = _
  simp [R,remD,add_mul,sum_mul,mul_div_assoc,mul_assoc]
private theorem rv_span (ε : ℝ) (N : ℕ) : unitVector - resVec ε N ∈ V := by
  rw [resVec,sub_add_cancel_left]
  exact V.neg_mem (V.sum_mem fun d _ => V.smul_mem _ (mode_mem d))
private theorem rv_bound (ε : ℝ) (N : ℕ) (B : ℝ)
    (hb : ∀ J : ℕ, ∑ n ∈ range J, R ε N n^2 / den n ≤ B) :
    ‖resVec ε N‖ ≤ |B|+1 := by
  have hh := (lp.hasSum_norm (p := 2) (by norm_num) (resVec ε N)).tendsto_sum_nat
  have he : (fun n => ‖resVec ε N n‖ ^ (2:ENNReal).toReal) =
      fun n => R ε N n^2 / den n := by
    funext n
    norm_num [rv_coord,Real.norm_eq_abs,mul_pow,scale_sq,div_eq_mul_inv]
  rw [he] at hh
  have hs : ‖resVec ε N‖^2 ≤ B := by
    simpa using le_of_tendsto hh (Eventually.of_forall hb)
  nlinarith [sq_nonneg (‖resVec ε N‖-1),sq_nonneg (‖resVec ε N‖-1/2),le_abs_self B,abs_nonneg B]

private theorem target_closure : unitVector ∈ V.topologicalClosure := by
  obtain ⟨B,hB⟩ := NymanBeurling.damped_moebius_bounded_mean_square
  have hchoose (j : ℕ) : ∃ (ε : ℝ) (N : ℕ),
      ‖resVec ε N‖ ≤ |B|+1 ∧ ∀ n ≤ j, |R ε N n| < 1/(j+1:ℝ) := by
    have hp := NymanBeurling.damped_moebius_finite_prefix_limit (j+1) (1/(j+1:ℝ)) (by positivity)
    obtain ⟨ε,hb,hp⟩ := (hB.and_eventually hp).exists
    obtain ⟨N,hb,hp⟩ := (hb.and_eventually hp).exists
    exact ⟨ε,N,rv_bound ε N B hb,fun n hn => hp (n+1) (mem_Ioc.mpr ⟨by omega,by omega⟩)⟩
  choose ε N hb hp using hchoose
  apply closed_span V unitVector (fun j => resVec (ε j) (N j)) (fun j => rv_span _ _) (|B|+1) hb
  intro i
  have ht : Tendsto (fun j => R (ε j) (N j) i) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    filter_upwards [eventually_ge_atTop i] with j hj using (hp j i hj).le
  simpa [rv_coord] using ht.mul_const (scale i)

private theorem approx_coeff (η : ℝ) (hη : 0<η) :
    ∃ (N : ℕ) (b : Fin N → ℝ), ∀ H' : ℕ,
      ∑ n ∈ range H', (1-∑ k : Fin N, b k*(((n+1)%(k.val+2):ℕ):ℝ)/(k.val+2:ℝ))^2 /
        ((n+1:ℝ)*(n+2:ℝ)) < η := by
  have hc : unitVector ∈ closure (V : Set H) := target_closure
  obtain ⟨y,hy,hnear⟩ := Metric.mem_closure_iff.mp hc (Real.sqrt η) (Real.sqrt_pos.mpr hη)
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  let N := c.support.sup id + 1
  have hsub : c.support ⊆ range N := fun k hk => mem_range.mpr (Nat.lt_succ_of_le (le_sup (f:=id) hk))
  let b : Fin N → ℝ := fun k => c k.val
  have hvec : ∑ k : Fin N, b k • mode (k.val+2) = y := by
    rw [show (∑ k : Fin N, b k • mode (k.val+2)) = ∑ k ∈ range N, c k • mode (k+2) by
      exact Fin.sum_univ_eq_sum_range (fun k => c k • mode (k+2)) N]
    rw [←hc]
    exact (sum_subset hsub (fun k _ hk => by simp [Finsupp.notMem_support_iff.mp hk])).symm
  have hcoord (n : ℕ) : y n = (∑ k : Fin N, b k*(((n+1)%(k.val+2):ℕ):ℝ)/(k.val+2:ℝ))*scale n := by
    let ev := lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n
    change ev y = _
    rw [←hvec,map_sum,sum_mul]
    apply sum_congr rfl
    intro k _
    rw [map_smul]
    change _ * (remD _ _ * _) = _
    simp [remD,mul_div_assoc,mul_assoc]
  have hs := lp.hasSum_norm (p:=2) (by norm_num) (unitVector-y)
  have he (n : ℕ) : ‖(unitVector-y) n‖ ^ (2:ENNReal).toReal =
      (1-∑ k : Fin N, b k*(((n+1)%(k.val+2):ℕ):ℝ)/(k.val+2:ℝ))^2/((n+1:ℝ)*(n+2:ℝ)) := by
    change ‖scale n - y n‖ ^ (2:ENNReal).toReal = _
    rw [hcoord,←one_sub_mul]
    norm_num [Real.norm_eq_abs,mul_pow,scale_sq,den,div_eq_mul_inv]
  refine ⟨N,b,fun H' => ?_⟩
  simp_rw [←he]
  apply (hs.summable.sum_le_tsum (range H') (fun _ _ => by positivity)).trans_lt
  rw [hs.tsum_eq]
  norm_num
  rw [dist_eq_norm] at hnear
  exact (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hnear |>.trans_eq (Real.sq_sqrt hη.le)

-- The final tail and rounding use the accepted certificate argument of submission 2f831c20.
theorem NymanBeurling.arbitrarily_small_remainder_certificates (J : ℕ) :
    ∃ (c : ℕ →₀ ℚ) (H : ℕ), ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) < 1/(J+1 : ℚ) := by
  classical
  let η : ℝ := 1 / (J+1 : ℝ)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N,b,happrox⟩ := approx_coeff (η/2) (by positivity)
  let B : ℝ := (1 + ∑ k : Fin N, |b k|)^2
  obtain ⟨H, hH⟩ := exists_nat_gt (B / (η/2))
  have htail : B / (H+1 : ℝ) < η/2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < H+1)).2
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < η/2)).1 hH
    nlinarith
  have hfinite : (∑ n ∈ Finset.range H,
      (1 - ∑ k : Fin N, b k * (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ))) < η/2 := happrox H
  obtain ⟨c, hc, hcost⟩ := NymanBeurling.real_certificate_has_rational_rounding N H b η
    (by change _ + B / (H+1 : ℝ) < η; linarith)
  refine ⟨c, H, ?_⟩
  apply (Rat.cast_lt (K := ℝ)).mp
  have hηcast : ((1 / (J+1 : ℚ) : ℚ) : ℝ) = η := by simp [η]
  rw [hηcast]
  exact hcost

end

-- Step 2: `NymanBeurling.arbitrarily_small_remainder_certificates` implies `MasulloRH.zero_free_right` (accepted reduction of `MasulloRH.zero_free_right`).
section

open scoped BigOperators

theorem MasulloRH.zero_free_right (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hpos : 0 < 2*s.re-1 := by linarith
  obtain ⟨J,hJ⟩ := exists_nat_gt (‖s‖^2 / (2*s.re-1))
  obtain ⟨c,H,hC⟩ := NymanBeurling.arbitrarily_small_remainder_certificates J
  let M : ℚ := ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ)
  change M < 1/(J+1 : ℚ) at hC
  have hc : (M:ℝ) < 1/(J+1:ℝ) := by
    have ht := (Rat.cast_lt (K := ℝ)).mpr hC
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_natCast] using ht
  have hh := NymanBeurling.finite_remainder_zero_obstruction s hs hs_one hz c H
  change 2*s.re-1 ≤ (M:ℝ)*‖s‖^2 at hh
  apply (not_lt_of_ge hh)
  calc
    _ ≤ (1/(J+1:ℝ))*‖s‖^2 := mul_le_mul_of_nonneg_right hc.le (sq_nonneg _)
    _ < 2*s.re-1 := by
      rw [one_div,inv_mul_eq_div,div_lt_iff₀ (by positivity)]
      have hh := (div_lt_iff₀ hpos).mp hJ
      nlinarith

end

-- Step 3: `MasulloRH.zero_free_right` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis := by
  have hright : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
    fun s hs hs1 => MasulloRH.zero_free_right s hs hs1
  refine riemannHypothesis_iff_zeros_in_strip_on_line.mpr (fun s hz h0 h1 => ?_)
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hneg : ∀ n : ℕ, s ≠ -(n : ℂ) := fun n h => by
      have hre := congrArg Complex.re h
      simp at hre
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub hneg hs1
    rw [hz, mul_zero] at hfe
    have hre : (1 / 2 : ℝ) < (1 - s).re := by simp; linarith
    have h1s : (1 - s) ≠ 1 := fun h => by
      have hre' := congrArg Complex.re h
      simp at hre'
      linarith
    exact hright (1 - s) hre h1s hfe
  · exact heq
  · exact absurd hz (hright s hgt hs1)

end
