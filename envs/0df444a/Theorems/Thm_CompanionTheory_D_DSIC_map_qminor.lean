-- Prove2me | Theorems.Thm_CompanionTheory_D_DSIC_map_qminor
-- name    : CompanionTheory.D.DSIC.map_qminor
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:09:58.506911+00:00
-- url     : https://prove2.me/theorems/f0e5c915-8f50-4e78-9662-073a61bc4b86
-- title:
--   DSIC: map qminor
-- statement:
--   The DSIC construction uses the map qminor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/Spread.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/Spread.lean#L15-L23

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

theorem CompanionTheory.D.DSIC.map_qminor {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) :
    f (qminor E a b u) = qminor (fun c d => f (E c d)) a b u := by sorry
