-- Prove2me | solution 1 for talagrand_tangent_sampling_appendix91_polynomial_scale_from_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-29T16:16:43.613255+00:00
-- url     : https://prove2.me/submissions/33948022-56f8-49e9-a7a9-062b723292a0

import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_tangent_sampling_deviation_candidates_bddAbove
import Definitions.Def_matrix_completion_talagrand
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

private lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _)
    (pow_nonneg (sub_nonneg.mpr hp_one) _)

private lemma tangentSamplingDeviation_nonneg
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 ≤ tangentSamplingDeviation Omega S p := by
  unfold tangentSamplingDeviation
  refine le_csSup (tangent_sampling_deviation_candidates_bddAbove Omega S p) ?_
  refine ⟨0, ?_, ?_, ?_⟩
  · ext i j
    simp [tangentProjection, leftSingularProjection, rightSingularProjection,
      twoSidedSingularProjection]
  · unfold frobeniusNorm frobeniusNormSq
    simp
  · unfold frobeniusNorm frobeniusNormSq
    simp [tangentProjection, leftSingularProjection, rightSingularProjection,
      twoSidedSingularProjection, samplingProjection]

private lemma bernoulliExpectation_tangentSamplingDeviation_nonneg
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1) (S : SVD M r) :
    0 ≤ bernoulliExpectation p
      (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        tangentSamplingDeviation Omega S p) := by
  unfold bernoulliExpectation
  exact Finset.sum_nonneg (fun Omega _ =>
    mul_nonneg (bernoulliObservationWeight_nonneg hp hp_one Omega)
      (tangentSamplingDeviation_nonneg Omega S p))

private lemma log_one_add_half_lower {t : ℝ} (ht : 0 ≤ t) :
    t / (2 + t) ≤ Real.log (1 + t / 2) := by
  have hpos : 0 < 1 + t / 2 := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hrewrite : 1 - (1 + t / 2)⁻¹ = t / (2 + t) := by
    field_simp [show (2 : ℝ) + t ≠ 0 by positivity]
    ring
  simpa [hrewrite] using h

private lemma appendix91_scalar_failure_bound
    {K C C' β μ₀ meanZ : ℝ} {n₁ n₂ r m : ℕ}
    (hK : 0 < K) (hCpos : 0 < C) (hCge_one : 1 ≤ C)
    (hCbig : 2 * K * (2 + C) ≤ C * C)
    (hC' : C ≤ C') (hβ : 2 < β)
    (hn₁ : 0 < n₁) (_hn₂ : 0 < n₂) (hr : 0 < r)
    (hmpos : 0 < m) (_hm : m ≤ n₁ * n₂)
    (hμ₀ : 1 ≤ μ₀)
    (hmLower : (m : ℝ) ≥
      C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
        (β * Real.log (↑(max n₁ n₂))))
    (hmean_nonneg : 0 ≤ meanZ) (hmean_le_one : meanZ ≤ 1) :
    let t := tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m
    let B := 2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)
    0 ≤ t ∧
      3 * Real.exp
        (-(t / (K * B)) *
          Real.log (1 + (B * t) / (B + B * meanZ))) ≤
        3 * Real.rpow (↑(max n₁ n₂)) (-β) := by
  let n : ℕ := max n₁ n₂
  let L : ℝ := β * Real.log (n : ℝ)
  let A : ℝ := μ₀ * (n : ℝ) * (r : ℝ) / (m : ℝ)
  let t : ℝ := tangentSamplingDeviationScale C β μ₀ n r m
  let B : ℝ := 2 * μ₀ * (n : ℝ) * (r : ℝ) / (m : ℝ)
  have hn_pos_nat : 0 < n := by
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hn_pos_nat)
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg hn_ge_one
  have hβ_nonneg : 0 ≤ β := by linarith
  have hL_nonneg : 0 ≤ L := by
    exact mul_nonneg hβ_nonneg hlog_nonneg
  have hμ₀_pos : 0 < μ₀ := by linarith
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hA_pos : 0 < A := by
    dsimp [A, n]
    positivity
  have hB_eq : B = 2 * A := by
    dsimp [B, A]
    ring
  have hB_pos : 0 < B := by
    rw [hB_eq]
    positivity
  have ht_nonneg : 0 ≤ t := by
    dsimp [t, tangentSamplingDeviationScale]
    exact mul_nonneg hCpos.le (Real.sqrt_nonneg _)
  have hC'_pos : 0 < C' := lt_of_lt_of_le hCpos hC'
  have hC'_ge_one : 1 ≤ C' := le_trans hCge_one hC'
  let Q : ℝ := μ₀ * (n : ℝ) * (r : ℝ) * L
  have hmLowerQ : C' * Q ≤ (m : ℝ) := by
    dsimp [Q, L, n]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmLower
  have hQ_div : Q / (m : ℝ) ≤ 1 / C' := by
    rw [div_le_div_iff₀ hm_pos hC'_pos]
    nlinarith [hmLowerQ]
  have hAL_eq : A * L = Q / (m : ℝ) := by
    dsimp [A, Q]
    ring_nf
  have hAL_le_inv : A * L ≤ 1 / C' := by
    simpa [hAL_eq] using hQ_div
  have hInv_le_one : 1 / C' ≤ 1 := by
    rw [div_le_one hC'_pos]
    exact hC'_ge_one
  have hAL_le_one : A * L ≤ 1 := le_trans hAL_le_inv hInv_le_one
  have hsqrt_le_one : Real.sqrt (A * L) ≤ 1 := by
    simpa using (Real.sqrt_le_one.mpr hAL_le_one)
  have ht_eq : t = C * Real.sqrt (A * L) := by
    dsimp [t, tangentSamplingDeviationScale, A, L]
    congr 1
    ring_nf
  have ht_le_C : t ≤ C := by
    rw [ht_eq]
    have hmul := mul_le_mul_of_nonneg_left hsqrt_le_one hCpos.le
    simpa using hmul
  have hAL_nonneg : 0 ≤ A * L := mul_nonneg hA_pos.le hL_nonneg
  have ht_sq : t * t = C * C * (A * L) := by
    rw [ht_eq]
    nlinarith [Real.sq_sqrt hAL_nonneg]
  let ratio : ℝ := (B * t) / (B + B * meanZ)
  have hmean_den_pos : 0 < 1 + meanZ := by linarith
  have hratio_eq : ratio = t / (1 + meanZ) := by
    dsimp [ratio]
    field_simp [hB_pos.ne', hmean_den_pos.ne']
  have hratio_ge_half : t / 2 ≤ ratio := by
    rw [hratio_eq]
    have hden_le_two : 1 + meanZ ≤ 2 := by linarith
    exact div_le_div_of_nonneg_left ht_nonneg hmean_den_pos hden_le_two
  have hlog_mono :
      Real.log (1 + t / 2) ≤ Real.log (1 + ratio) := by
    have hleft_pos : 0 < 1 + t / 2 := by positivity
    refine Real.log_le_log hleft_pos ?_
    linarith
  have hlog_lower : t / (2 + t) ≤ Real.log (1 + ratio) :=
    (log_one_add_half_lower ht_nonneg).trans hlog_mono
  let E : ℝ := (t / (K * B)) * Real.log (1 + ratio)
  have hcoef_nonneg : 0 ≤ t / (K * B) := by positivity
  have hE_lower :
      (t / (K * B)) * (t / (2 + t)) ≤ E := by
    dsimp [E]
    exact mul_le_mul_of_nonneg_left hlog_lower hcoef_nonneg
  have hcore : L ≤ (t / (K * B)) * (t / (2 + t)) := by
    have htwo_t_pos : 0 < 2 + t := by positivity
    have hprod_eq :
        (t / (K * B)) * (t / (2 + t)) =
          (t * t) / (K * B * (2 + t)) := by
      field_simp [hK.ne', hB_pos.ne', htwo_t_pos.ne']
    rw [hprod_eq]
    have hden_pos : 0 < K * B * (2 + t) := by positivity
    rw [le_div_iff₀ hden_pos]
    have hfactor : 2 * K * (2 + t) ≤ C * C := by
      have h2t : 2 + t ≤ 2 + C := by linarith
      have hstep : 2 * K * (2 + t) ≤ 2 * K * (2 + C) := by
        nlinarith [hK, h2t]
      exact le_trans hstep hCbig
    have hmain :
        (A * L) * (2 * K * (2 + t)) ≤ (A * L) * (C * C) :=
      mul_le_mul_of_nonneg_left hfactor hAL_nonneg
    calc
      L * (K * B * (2 + t))
          = (A * L) * (2 * K * (2 + t)) := by
            rw [hB_eq]
            ring
      _ ≤ (A * L) * (C * C) := hmain
      _ = t * t := by
            rw [ht_sq]
            ring
  have hExponent : L ≤ E := hcore.trans hE_lower
  have hExp :
      Real.exp (-E) ≤ Real.rpow (n : ℝ) (-β) := by
    change Real.exp (-E) ≤ (n : ℝ) ^ (-β)
    rw [Real.rpow_def_of_pos hn_pos]
    apply Real.exp_le_exp.mpr
    have hneg : -E ≤ -L := by linarith
    have hrewrite : Real.log (n : ℝ) * (-β) = -L := by
      dsimp [L]
      ring
    simpa [hrewrite] using hneg
  have hFailure :
      3 * Real.exp (-E) ≤ 3 * Real.rpow (n : ℝ) (-β) :=
    mul_le_mul_of_nonneg_left hExp (by norm_num)
  refine ⟨ht_nonneg, ?_⟩
  simpa [t, B, E, ratio, n] using hFailure

theorem solution
    (K : ℝ) :
    0 < K →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                |tangentSamplingDeviation Omega S
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) -
                    bernoulliExpectation
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                      (fun Omega' =>
                        tangentSamplingDeviation Omega' S
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))| ≤ t) ≥
            1 -
              3 * Real.exp
                (-(t / (K *
                    (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)))) *
                  Real.log
                    (1 +
                      ((2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) * t) /
                        ((2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) +
                          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) *
                            bernoulliExpectation
                              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                              (fun Omega' =>
                                tangentSamplingDeviation Omega' S
                                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))))))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) +
                  tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hK
  let C : ℝ := 16 * (K + 1) ^ 2
  refine ⟨C, 3, ?_, by norm_num, ?_⟩
  · positivity
  intro C' hC' β hβ n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hmpos hm hμ₀ hmLower hEZ _hInc _hVar hLog
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let meanZ : ℝ :=
    bernoulliExpectation p (fun Omega' => tangentSamplingDeviation Omega' S p)
  let t : ℝ := tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m
  let B : ℝ := 2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)
  have hCge_one : 1 ≤ C := by
    have hkp1 : 1 < K + 1 := by linarith
    have hsquare : 1 ≤ (K + 1) ^ 2 := by nlinarith
    nlinarith
  have hCbig : 2 * K * (2 + C) ≤ C * C := by
    have hkp1 : 1 ≤ K + 1 := by linarith
    have hKle : K ≤ K + 1 := by linarith
    have hCeq : C = 16 * (K + 1) ^ 2 := rfl
    nlinarith [sq_nonneg (K + 1)]
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp_nonneg, hp_le_one⟩
  have hmean_nonneg : 0 ≤ meanZ := by
    simpa [p, meanZ] using
      bernoulliExpectation_tangentSamplingDeviation_nonneg
        (p := p) hp_nonneg hp_le_one S
  have hmean_le_one : meanZ ≤ 1 := by
    simpa [p, meanZ] using hEZ
  rcases appendix91_scalar_failure_bound
      (K := K) (C := C) (C' := C') (β := β)
      (μ₀ := μ₀) (meanZ := meanZ)
      (n₁ := n₁) (n₂ := n₂) (r := r) (m := m)
      hK (by positivity) hCge_one hCbig hC' hβ
      hn₁ hn₂ hr hmpos hm hμ₀ hmLower hmean_nonneg hmean_le_one with
    ⟨ht_nonneg, hFailure⟩
  have hAbsProb :
      bernoulliEventProb p
          (fun Omega =>
            |tangentSamplingDeviation Omega S p - meanZ| ≤ t) ≥
        1 - 3 * Real.exp
          (-(t / (K * B)) *
            Real.log (1 + (B * t) / (B + B * meanZ))) := by
    simpa [p, meanZ, t, B] using hLog t ht_nonneg
  have hPolyProb :
      bernoulliEventProb p
          (fun Omega =>
            |tangentSamplingDeviation Omega S p - meanZ| ≤ t) ≥
        1 - 3 * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have hLower :
        1 - 3 * Real.rpow (↑(max n₁ n₂)) (-β) ≤
          1 - 3 * Real.exp
            (-(t / (K * B)) *
              Real.log (1 + (B * t) / (B + B * meanZ))) := by
      linarith [hFailure]
    exact le_trans hLower hAbsProb
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            |tangentSamplingDeviation Omega S p - meanZ| ≤ t) ≤
        bernoulliEventProb p
          (fun Omega =>
            TangentSamplingDeviationBound Omega S p (meanZ + t)) := by
    exact bernoulli_event_probability_mono p _ _ hp_nonneg hp_le_one
      (fun Omega hOmega => by
        have hUpper : tangentSamplingDeviation Omega S p - meanZ ≤ t :=
          (abs_le.mp hOmega).2
        have hOneSided : tangentSamplingDeviation Omega S p ≤ meanZ + t := by
          linarith
        simpa [TangentSamplingDeviationBound, meanZ, t] using hOneSided)
  exact le_trans hPolyProb hMono
