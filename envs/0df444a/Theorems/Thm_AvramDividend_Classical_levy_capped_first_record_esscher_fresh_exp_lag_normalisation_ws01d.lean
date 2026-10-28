-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_first_record_esscher_fresh_exp_lag_normalisation_ws01d
-- name    : AvramDividend.Classical.levy_capped_first_record_esscher_fresh_exp_lag_normalisation_ws01d
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:21:01.998027+00:00
-- url     : https://prove2.me/theorems/95ddd7f7-9553-499e-8cdc-8082f3eda8f3
-- title:
--   Genuine independent exponential future-lag Esscher normalisation after a capped first upper record
-- statement:
--   For a spectrally negative Lévy process under P, its genuine capped first strict upper record τ_N and event T_b<N, the expectation under the genuine path-product-independent real exponential clock E~Exp(p) of any measurable record discount multiplied by exp(phi*(X_(τ_N+E)−X_τ_N)−qE) is exactly the P-expectation of the same stopped discount and record indicator, when phi≥0 and ψ(phi)=q. Uses actual product P⊗expMeasure p, not unspecified Esscher law. It is the random-lag extension of the already Proved deterministic-lag capped-first-record theorem, and is needed to normalise a genuine random-terminal Esscher first-passage likelihood.
-- source:
--   Canonical fixed-lag normalisation 4685fca7-a162-48e0-8f56-0431c4a99764; pinned Mathlib product Tonelli and expMeasure finite probability; canonical joint Lévy path-time and capped record clock measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_capped_first_record_esscher_future_lag_normalisation_ws01d
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_capped_first_record_esscher_fresh_exp_lag_normalisation_ws01d
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N : ℝ≥0)
    (p : ℝ) (hp : 0 < p)
    (phi q : ℝ) (hphi : 0 ≤ phi) (hroot : X.ψ phi = q)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ z : Ω × ℝ, if z.1 ∈ A then discount (τ z.1) *
       ENNReal.ofReal (Real.exp
         (phi * (X.X (τ z.1 + z.2.toNNReal) z.1 -
            X.X (τ z.1) z.1) -
          (z.2.toNNReal : ℝ) * q)) else 0
       ∂(P.prod (ProbabilityTheory.expMeasure p))) =
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P)) := by sorry
