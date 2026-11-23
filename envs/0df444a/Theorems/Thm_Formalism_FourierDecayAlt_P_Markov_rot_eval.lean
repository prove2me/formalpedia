-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_rot_eval
-- name    : Formalism.FourierDecayAlt.P.Markov.rot_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:49.052841+00:00
-- url     : https://prove2.me/theorems/8fefb564-ca4a-4d46-96f1-7ce191f1db90
-- title:
--   Markov: rot eval
-- statement:
--   The Markov construction uses the rot eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L149-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L149-L156

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset

theorem Formalism.FourierDecayAlt.P.Markov.rot_eval (a b : ℝ) (m : ℕ) (y z : ℝ) (h : y ^ 2 + z ^ 2 = 1) :
    (a * y + b * z) ^ m = (rot a b m).1.eval y + z * (rot a b m).2.eval y := by sorry
