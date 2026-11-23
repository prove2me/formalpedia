-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_stdPoly_update
-- name    : CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_update
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:53.34419+00:00
-- url     : https://prove2.me/theorems/0a7b3fd8-4387-497a-9c1f-444d780fcd5b
-- title:
--   Fin Of PIAux: std Poly update
-- statement:
--   The Fin Of PIAux construction uses the std Poly update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L155-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L155-L170

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.FinOfPIAux
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_update {R : Type*} [Ring R] (E : R) {M : ℕ} (a : Fin M → R) (j : Fin M) :
    ∃ A B : Equiv.Perm (Fin M) → R, ∀ T, stdPoly E (Function.update a j T) = ∑ π, A π * T * B π := by sorry
