-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_word_cases
-- name    : CompanionTheory.D.gk.admitted.FinOfPIAux.word_cases
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:19.110815+00:00
-- url     : https://prove2.me/theorems/3d94eb83-3497-4717-91ed-8348e639a4de
-- title:
--   Fin Of PIAux: word cases
-- statement:
--   The Fin Of PIAux construction uses the word cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L218-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L218-L236

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
variable (E : H →L[ℂ] H) (M : ℕ) (φ : ℕ → H →L[ℂ] ℂ) (x : ℕ → H)
omit [CompleteSpace H]

theorem CompanionTheory.D.gk.admitted.FinOfPIAux.word_cases (hφ : ∀ i ≤ M, ∀ j ≤ M, φ i (E (x j)) = if i = j then 1 else 0) (l : List ℕ)
    (hl : ∀ a ∈ l, a < M) :
    word E (l.map fun a => (φ (a + 1)).smulRight (x a)) (x M) = 0 ∨
      ∃ k, k + l.length = M ∧ l = List.range' k l.length := by sorry
