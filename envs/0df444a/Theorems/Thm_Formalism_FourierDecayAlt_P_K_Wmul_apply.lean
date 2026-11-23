-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_K_Wmul_apply
-- name    : Formalism.FourierDecayAlt.P.K.Wmul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:38.946305+00:00
-- url     : https://prove2.me/theorems/1f4e3625-0d09-4674-b320-d7d6bdb8b528
-- title:
--   K: Wmul apply
-- statement:
--   The K construction uses the Wmul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L62-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AntidiagMulDiagonal.lean#L62-L73

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

theorem Formalism.FourierDecayAlt.P.K.Wmul_apply (c : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (i j : Fin n) :
    ((w0 n * diagonal d) * c : Matrix (Fin n) (Fin n) K) i j = d (Fin.rev i) * c (Fin.rev i) j := by sorry
