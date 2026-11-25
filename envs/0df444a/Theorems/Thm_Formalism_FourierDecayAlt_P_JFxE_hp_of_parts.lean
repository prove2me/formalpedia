-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_hp_of_parts
-- name    : Formalism.FourierDecayAlt.P.JFxE.hp_of_parts
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:34:30.862898+00:00
-- url     : https://prove2.me/theorems/575c09b2-5b26-4eb5-86d3-6e26f2de9819
-- title:
--   JFx E: hp of parts
-- statement:
--   The JFx E construction uses the hp of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L97-L101

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxE.hp_of_parts {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) :
    hpart1 (Hpk k r) (X + Complex.I • Y) = X ∧ hpart2 (Hpk k r) (X + Complex.I • Y) = Y := by sorry
