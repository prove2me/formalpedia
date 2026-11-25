-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_inner_translate
-- name    : CompanionTheory.LimBd.Main.inner_translate
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:18:15.539228+00:00
-- url     : https://prove2.me/theorems/faa5cff4-1af6-5f57-a906-7e4b7c1b23d0
-- title:
--   Main: inner translate
-- statement:
--   The Main construction uses the inner translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/BetaAtInfinityZero.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/BetaAtInfinityZero.lean#L33-L46

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_BetaAtInfinityZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk MeasureTheory
open scoped InnerProductSpace

theorem CompanionTheory.LimBd.Main.inner_translate {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (UH (Hpk k r)) σ) {a g b : B.Mat k r} (ha : a ∈ UH (Hpk k r))
    (hg : g ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) (v w : H) :
    ⟪w, σ (a * g * b) v⟫_ℂ = ⟪σ a⁻¹ w, σ g (σ b v)⟫_ℂ := by sorry
