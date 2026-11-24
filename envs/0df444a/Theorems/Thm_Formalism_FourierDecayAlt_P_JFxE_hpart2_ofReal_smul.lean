-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_hpart2_ofReal_smul
-- name    : Formalism.FourierDecayAlt.P.JFxE.hpart2_ofReal_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:20:25.481477+00:00
-- url     : https://prove2.me/theorems/0cabcd83-b68a-43ff-bbea-520ce18a1621
-- title:
--   JFx E: hpart2 of Real smul
-- statement:
--   The JFx E construction uses the hpart2 of Real smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L61-L64

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

theorem Formalism.FourierDecayAlt.P.JFxE.hpart2_ofReal_smul (x : ℝ) (Z : Mat k r) : hpart2 (Hpk k r) ((x : ℂ) • Z) = (x : ℂ) • hpart2 (Hpk k r) Z := by sorry
