-- Prove2me | Theorems.Thm_CompanionTheory_D_DSIC_qminor_mem
-- name    : CompanionTheory.D.DSIC.qminor_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:10:49.001037+00:00
-- url     : https://prove2.me/theorems/7955317b-5745-4c19-8072-468819715eef
-- title:
--   DSIC: qminor mem
-- statement:
--   The DSIC construction uses the qminor mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/Spread.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/Spread.lean#L25-L32

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

theorem CompanionTheory.D.DSIC.qminor_mem {A : Type} [Ring A] [Algebra ℂ A] (T : Subalgebra ℂ A) {n t : ℕ}
    (E : Fin n → Fin n → A) (hE : ∀ c d, E c d ∈ T) (a b : Fin t → Fin n) (u : ℂ) : qminor E a b u ∈ T := by sorry
