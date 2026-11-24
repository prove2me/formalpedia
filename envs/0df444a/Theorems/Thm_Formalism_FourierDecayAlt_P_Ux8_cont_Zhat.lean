-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_cont_Zhat
-- name    : Formalism.FourierDecayAlt.P.Ux8.cont_Zhat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:36:22.221078+00:00
-- url     : https://prove2.me/theorems/383ff075-ce38-46a7-ab09-f61694a2b7ba
-- title:
--   Ux8: cont Zhat
-- statement:
--   The Ux8 construction uses the cont Zhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L489-L492
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L489-L492

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.Ux8.cont_Zhat (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    Continuous fun g : B.Mat k r => Zhat k r z z' g a b := by sorry
