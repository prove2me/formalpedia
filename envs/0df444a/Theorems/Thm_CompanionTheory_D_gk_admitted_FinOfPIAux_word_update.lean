-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_word_update
-- name    : CompanionTheory.D.gk.admitted.FinOfPIAux.word_update
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:29.479667+00:00
-- url     : https://prove2.me/theorems/b86c773f-4b93-480e-adf5-32af1b2e309d
-- title:
--   Fin Of PIAux: word update
-- statement:
--   The Fin Of PIAux construction uses the word update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L137-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L137-L153

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

theorem CompanionTheory.D.gk.admitted.FinOfPIAux.word_update {R : Type*} [Ring R] (E : R) {n : ℕ} (f : Fin n → R) (k : Fin n) :
    ∃ A B : R, ∀ T, word E (List.ofFn (Function.update f k T)) = A * T * B := by sorry
