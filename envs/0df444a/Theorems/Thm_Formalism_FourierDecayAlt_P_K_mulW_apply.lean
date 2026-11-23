-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_K_mulW_apply
-- name    : Formalism.FourierDecayAlt.P.K.mulW_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:12.327935+00:00
-- url     : https://prove2.me/theorems/d757b467-2585-48f4-a52c-d4a5e5b90c17
-- title:
--   K: mul W apply
-- statement:
--   The K construction uses the mul W apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L53-L60

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.K
open Matrix Finset Real Formalism.FourierDecayAlt.K
variable {K : Type} [Field K] {n : ℕ}

theorem Formalism.FourierDecayAlt.P.K.mulW_apply (a : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (i j : Fin n) :
    (a * (w0 n * diagonal d) : Matrix (Fin n) (Fin n) K) i j = a i (Fin.rev j) * d j := by sorry
