-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_kronecker_embed_mul_apply
-- name    : Formalism.FourierDecayAlt.P.Wd2.kronecker_embed_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:41.01817+00:00
-- url     : https://prove2.me/theorems/6b0df418-a3d6-409a-998c-08d2bf0e06cd
-- title:
--   Wd2: kronecker embed mul apply
-- statement:
--   The Wd2 construction uses the kronecker embed mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L54-L57

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K B : Type} [CommRing K] [Ring B] [Algebra K B]

theorem Formalism.FourierDecayAlt.P.Wd2.kronecker_embed_mul_apply (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E2 N * E1 M) (i, k) (j, l) = N k l * M i j := by sorry
