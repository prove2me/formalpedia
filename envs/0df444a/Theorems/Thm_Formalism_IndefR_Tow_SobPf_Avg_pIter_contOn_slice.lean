-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_SobPf_Avg_pIter_contOn_slice
-- name    : Formalism.IndefR.Tow.SobPf.Avg.pIter_contOn_slice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:04:55.023996+00:00
-- url     : https://prove2.me/theorems/a231fc11-cb77-4e0f-ae8e-512fd7d8b975
-- title:
--   Avg: p Iter cont On slice
-- statement:
--   The Avg construction uses the p Iter cont On slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/HasFDerivAtIntegralPIter.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/HasFDerivAtIntegralPIter.lean#L27-L31

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
omit [CompleteSpace E]

theorem Formalism.IndefR.Tow.SobPf.Avg.pIter_contOn_slice {K : Set X} {Φ : (Fin m → ℝ) → X → E} {j : ℕ}
    (hc : ContinuousOn (fun q : (Fin m → ℝ) × X => pIter Φ j q.1 q.2) (Set.univ ×ˢ K)) (t : Fin m → ℝ) :
    ContinuousOn (fun k => pIter Φ j t k) K := by sorry
