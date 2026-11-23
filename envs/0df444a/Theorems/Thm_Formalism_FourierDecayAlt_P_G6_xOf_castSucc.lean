-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G6_xOf_castSucc
-- name    : Formalism.FourierDecayAlt.P.G6.xOf_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:21.185799+00:00
-- url     : https://prove2.me/theorems/f537dd8e-6594-4a6d-8be9-926a98fb778c
-- title:
--   G6: x Of cast Succ
-- statement:
--   The G6 construction uses the x Of cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RemainderNormLeStrictUpper.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RemainderNormLeStrictUpper.lean#L23-L25

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G6
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G6.xOf_castSucc {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ)
    (k : Fin m) : xOf X B k.castSucc = X k.castSucc k.succ := by sorry
