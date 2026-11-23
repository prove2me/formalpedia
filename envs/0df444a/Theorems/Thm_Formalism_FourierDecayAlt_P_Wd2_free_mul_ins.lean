-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_free_mul_ins
-- name    : Formalism.FourierDecayAlt.P.Wd2.free_mul_ins
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:59.99566+00:00
-- url     : https://prove2.me/theorems/7039ae6b-cdf2-4ab4-aa78-7b02531398e0
-- title:
--   Wd2: free mul ins
-- statement:
--   The Wd2 construction uses the free mul ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L86-L93

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
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd2.free_mul_ins (a : S) (x : SlopeTestRemainingChoices S A) (hx : FreeOf a x) (N : M2 (SlopeTestRemainingChoices S A)) :
    x * ins a N = ins a (Matrix.of fun k l => x * N k l) := by sorry
