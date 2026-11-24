-- Prove2me | Theorems.Thm_CompanionTheory_D_DSIC_qminor_intertwine
-- name    : CompanionTheory.D.DSIC.qminor_intertwine
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:09:58.948865+00:00
-- url     : https://prove2.me/theorems/00745759-727e-4bb6-8961-503aa3a58980
-- title:
--   DSIC: qminor intertwine
-- statement:
--   The DSIC construction uses the qminor intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/Spread.lean#L108-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/Spread.lean#L108-L125

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovDet
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovLin
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_Spread
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.DSIC
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem CompanionTheory.D.DSIC.qminor_intertwine {V : Type} [AddCommGroup V] [Module ℂ V] {n t : ℕ} (τ : Module.End ℂ V)
    (E E' : Fin n → Fin n → Module.End ℂ V) (h : ∀ a b, τ * E a b = E' a b * τ) (a b : Fin t → Fin n) (u : ℂ) :
    τ * qminor E a b u = qminor E' a b u * τ := by sorry
