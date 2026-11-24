-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_SobPf_Avg_hasFDerivAt_pIter
-- name    : Formalism.IndefR.Tow.SobPf.Avg.hasFDerivAt_pIter
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:21.354501+00:00
-- url     : https://prove2.me/theorems/e4046a3f-de64-4831-99f8-518e7ffe3e93
-- title:
--   Avg: has FDeriv At p Iter
-- statement:
--   The Avg construction uses the has FDeriv At p Iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/HasFDerivAtIntegralPIter.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/HasFDerivAtIntegralPIter.lean#L36-L44

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_HasFDerivAtIntegralPIter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open Formalism Formalism.IndefR Formalism.IndefR.Tow Formalism.IndefR.Tow.SobPf Formalism.IndefR.Tow.SobPf.Avg
variable {m : ℕ} {X E : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem Formalism.IndefR.Tow.SobPf.Avg.hasFDerivAt_pIter {Φ : (Fin m → ℝ) → X → E} {k : X} (hΦ : ContDiff ℝ ∞ fun t => Φ t k) (j : ℕ)
    (t : Fin m → ℝ) :
    HasFDerivAt (fun t => pIter Φ j t k)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Fin m → ℝ) E (pIter Φ (j + 1) t k)) t := by sorry
