-- Prove2me | Theorems.Thm_Formalism_IndefR_Tow_SobPf_Avg_ae_mem_of_compl
-- name    : Formalism.IndefR.Tow.SobPf.Avg.ae_mem_of_compl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:43.186558+00:00
-- url     : https://prove2.me/theorems/9ef02e92-928f-4e33-ade7-3551fb4cf674
-- title:
--   Avg: ae mem of compl
-- statement:
--   The Avg construction uses the ae mem of compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/HasFDerivAtIntegralPIter.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/HasFDerivAtIntegralPIter.lean#L18-L18

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
omit [SecondCountableTopology X] [OpensMeasurableSpace X] [NormedSpace ℝ E] [CompleteSpace E]

theorem Formalism.IndefR.Tow.SobPf.Avg.ae_mem_of_compl {μ : Measure X} {K : Set X} (hμK : μ Kᶜ = 0) : ∀ᵐ x ∂μ, x ∈ K := by sorry
