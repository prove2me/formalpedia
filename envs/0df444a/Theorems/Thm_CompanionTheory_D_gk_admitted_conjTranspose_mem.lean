-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_conjTranspose_mem
-- name    : CompanionTheory.D.gk.admitted.conjTranspose_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:14.873493+00:00
-- url     : https://prove2.me/theorems/97eae8f8-77e1-4e32-9bb5-4275e8a33d05
-- title:
--   admitted: conj Transpose mem
-- statement:
--   The admitted construction uses the conj Transpose mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/AdmissibleOfFiniteRank.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/AdmissibleOfFiniteRank.lean#L19-L25

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_InPCommutatorOfInK
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfFiniteRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {n : ℕ} {ε : Fin n → Bool}

theorem CompanionTheory.D.gk.admitted.conjTranspose_mem {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ UJset ε) : mᴴ ∈ UJset ε := by sorry
