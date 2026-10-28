-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_first_record_esscher_future_lag_normalisation_ws01d
-- name    : AvramDividend.Classical.levy_capped_first_record_esscher_future_lag_normalisation_ws01d
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:17:29.651633+00:00
-- url     : https://prove2.me/theorems/4685fca7-a162-48e0-8f56-0431c4a99764
-- title:
--   Capped first-record future Esscher exponential has unit conditional weight at every deterministic lag
-- statement:
--   For a genuine spectrally negative Lévy process and finite cap N, the uncensored strict first upper record event is measurable at the stopped history. Under the original probability P, any nonnegative measurable function of that capped first-record stopping age factors from the normalised exponential of a future increment at each fixed lag u. The moment normalisation uses the exact Lévy Laplace exponent ψ(phi)=q, and yields equality of the weighted stopped-history expectation with and without the future exponential. This is a necessary fixed-lag ingredient for a true finite-rate random-terminal Esscher stopping transfer; it does not identify an unproved variable observation clock or assume global Q_phi.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), section 2.1, equations (2.2)-(2.3), https://purehost.bath.ac.uk/ws/portalfiles/portal/9893933/Kyprianou_Levy_processes_2012.pdf; accepted capped first-record future reward factorisation 481d46a9-9eee-447f-ba81-eb05367eff3a and SpectrallyNegativeLevy.laplace.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_firstRecord_uncensored_discountedFutureReward_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_capped_first_record_esscher_future_lag_normalisation_ws01d
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N u : ℝ≥0)
    (phi q : ℝ) (hphi : 0 ≤ phi) (hroot : X.ψ phi = q)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) *
       ENNReal.ofReal (Real.exp
         (phi * (X.X (τ ω + u) ω - X.X (τ ω) ω) -
            (u : ℝ) * q))
       else 0 ∂P) =
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P)) := by sorry
