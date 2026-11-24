-- Prove2me | Theorems.Thm_CompanionTheory_D_DSIC_qdet_adj
-- name    : CompanionTheory.D.DSIC.qdet_adj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:10:10.973025+00:00
-- url     : https://prove2.me/theorems/f04577ea-2e8d-4efa-a3d4-af54481fadcf
-- title:
--   DSIC: qdet adj
-- statement:
--   The DSIC construction uses the qdet adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/Spread.lean#L53-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/Spread.lean#L53-L104

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem CompanionTheory.D.DSIC.qdet_adj {n : ℕ} {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E)
    (hU : IsUnitary ε E) (w : ℂ) (x y : V) : ⟪qdet E w x, y⟫_ℂ = ⟪x, qdet E (star w) y⟫_ℂ := by sorry
