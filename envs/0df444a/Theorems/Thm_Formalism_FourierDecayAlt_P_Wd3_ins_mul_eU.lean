-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul_eU
-- name    : Formalism.FourierDecayAlt.P.Wd3.ins_mul_eU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:13.405812+00:00
-- url     : https://prove2.me/theorems/af72f749-3e35-47e4-b313-88f1df0f0787
-- title:
--   Wd3: ins mul e U
-- statement:
--   The Wd3 construction uses the ins mul e U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L68-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L68-L83

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd3
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd3.ins_mul_eU (a : S) (j k : Fin 2) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m)
    (hN : FreeOf2 a N) :
    ins a N * (m * eU a j k) = ∑ r, eU a r k * (N r j * m) := by sorry
