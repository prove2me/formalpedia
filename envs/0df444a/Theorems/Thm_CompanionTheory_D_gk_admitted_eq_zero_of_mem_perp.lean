-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_eq_zero_of_mem_perp
-- name    : CompanionTheory.D.gk.admitted.eq_zero_of_mem_perp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:47.095625+00:00
-- url     : https://prove2.me/theorems/eb71695f-2076-4179-9632-a16f2eac0c2f
-- title:
--   admitted: eq zero of mem perp
-- statement:
--   The admitted construction uses the eq zero of mem perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GoodPI.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GoodPI.lean#L92-L93

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
open ComplexOrder

theorem CompanionTheory.D.gk.admitted.eq_zero_of_mem_perp {T : Submodule ℂ (ι → ℂ)} {y : ι → ℂ} (h1 : y ∈ T) (h2 : y ∈ perp T) : y = 0 := by sorry
