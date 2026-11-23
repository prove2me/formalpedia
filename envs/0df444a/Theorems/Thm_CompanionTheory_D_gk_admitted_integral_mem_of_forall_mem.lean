-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_integral_mem_of_forall_mem
-- name    : CompanionTheory.D.gk.admitted.integral_mem_of_forall_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:31.863571+00:00
-- url     : https://prove2.me/theorems/f2c2da56-d553-4933-afe6-cae6860edd55
-- title:
--   admitted: integral mem of forall mem
-- statement:
--   The admitted construction uses the integral mem of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GoodPI.lean#L129-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GoodPI.lean#L129-L137

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GoodPI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem CompanionTheory.D.gk.admitted.integral_mem_of_forall_mem {X : Type} [MeasurableSpace X] (μ : Measure X) (W : Submodule ℂ (ι → ℂ))
    (f : X → ι → ℂ) (hf : Integrable f μ) (hW : ∀ x, f x ∈ W) : ∫ x, f x ∂μ ∈ W := by sorry
