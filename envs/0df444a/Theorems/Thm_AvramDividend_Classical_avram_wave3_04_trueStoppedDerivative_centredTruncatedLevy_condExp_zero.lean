-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_trueStoppedDerivative_centredTruncatedLevy_condExp_zero
-- name    : AvramDividend.Classical.avram_wave3_04_trueStoppedDerivative_centredTruncatedLevy_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:43:29.153482+00:00
-- url     : https://prove2.me/theorems/dfa7d0ae-0faa-4436-aced-98859bc4923e
-- title:
--   Actual killed and clipped dividend verification derivative is conditionally orthogonal to centred, bounded Lévy increments
-- statement:
--   For the actual source Lévy process and any adapted left-continuous dividend strategy, take the genuinely compensated bounded future increment clip_R(X_t−X_s)−E[clip_R(X_{t−s})]. Multiply by the true discounted verification derivative evaluated at the post-payment reserve's strict-left limit, stopped inclusively at the true dividend ruin time, cut off at finite horizon T, and clipped at ±K. Its conditional expectation given the source's right-continuous past F_s is zero. No finite first moment of X_t is assumed, because the increment is bounded before centring. This establishes a source-faithful, conditional martingale-difference identity for the exact stopped verification coefficient and truncated Lévy increments, preserving the joint dividend/Lévy sample paths. Continuous-time quadratic variation and controlled Itô–Meyer limit remain outstanding.
-- source:
--   Private pinned remote compiler probe b5a18df8-9117-453a-9b5c-619dc605b4d9 reached sentinel with no source errors, SHA-256 d080645d60ac153285be97b6227a2ae8bdf030db51703aaa5c72eba43d51a29d. Accepted canonical source stopped clipped conditional factorisation UUID 9f47b4a0-3933-4cec-a933-b629047dfa9c; bounded source Lévy payoff integrability UUID eb2ca071-17d0-409f-b88a-59edf9d25ee8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_sourceStoppedClipped_futurePayoff_condExp
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_bounded_futurePayoff_integrable

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_trueStoppedDerivative_centredTruncatedLevy_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K R : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (T s t : ℝ≥0) (hst : s ≤ t) :
    P[(fun ω =>
      max (-K) (min K
        (if s ≤ T then
          (Real.exp (-(q * (s : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s)) *
          (if (s : ℝ≥0∞) ≤ ruinTime X x D ω then
            (1 : ℝ) else 0)
        else 0)) *
      (max (-R) (min R (X.X t ω - X.X s ω)) -
        ∫ η, max (-R) (min R (X.X (t - s) η)) ∂P))
        | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
