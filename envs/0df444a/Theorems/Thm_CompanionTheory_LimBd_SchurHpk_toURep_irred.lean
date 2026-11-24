-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_SchurHpk_toURep_irred
-- name    : CompanionTheory.LimBd.SchurHpk.toURep_irred
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:27:41.527173+00:00
-- url     : https://prove2.me/theorems/f4716e82-768b-4310-9ef6-81a97099513c
-- title:
--   Schur Hpk: to URep irred
-- statement:
--   The Schur Hpk construction uses the to URep irred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L178-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L178-L184

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

theorem CompanionTheory.LimBd.SchurHpk.toURep_irred (hP : IsCayley k r ε P)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (hσ : IsURepOn (UH (Hpk k r)) σ) [Nontrivial H] (hi : IsIrredOn (UH (Hpk k r)) σ) :
    (toURep hP σ hσ).IsIrreducible := by sorry
