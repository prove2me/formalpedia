-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_density_preserves_brownian_continuous_paths
-- name    : AppliedSDE.SarkkaSolin.girsanov_density_preserves_brownian_continuous_paths
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:14:15.971147+00:00
-- url     : https://prove2.me/theorems/abe77ee1-fa46-4149-a722-2a109a881636
-- title:
--   Continuous Brownian paths remain almost sure under every absolutely continuous density change
-- statement:
--   An almost surely continuous Brownian motion retains that almost-sure path continuity under any measure obtained by weighting its original probability measure with a nonnegative density ENNReal.ofReal(Z). This follows from absolute continuity of withDensity; no martingale or Girsanov hypotheses are required.
-- source:
--   Sarkka and Solin (2019), Girsanov shifted Brownian motion; Mathlib withDensity_absolutelyContinuous.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem AppliedSDE.SarkkaSolin.girsanov_density_preserves_brownian_continuous_paths
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (Z : Ω -> ℝ) :
    ∀ᵐ omega ∂(P.withDensity (fun omega => ENNReal.ofReal (Z omega))),
      Continuous (fun t : ℝ => W.W t omega) := by
  sorry
