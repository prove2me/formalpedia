-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_stdPoly_apply
-- name    : CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:07.656394+00:00
-- url     : https://prove2.me/theorems/a0ab7de8-a5dc-4583-bcee-5b2c30265d6e
-- title:
--   Fin Of PIAux: std Poly apply
-- statement:
--   The Fin Of PIAux construction uses the std Poly apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L242-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L242-L263

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

theorem CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_apply (hφ : ∀ i ≤ M, ∀ j ≤ M, φ i (E (x j)) = if i = j then 1 else 0) :
    stdPoly E (fun a : Fin M => (φ (a + 1)).smulRight (x a)) (x M) = E (x 0) := by sorry
