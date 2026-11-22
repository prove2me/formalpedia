-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul
-- name    : Formalism.FourierDecayAlt.P.Wd3.ins_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:45.967498+00:00
-- url     : https://prove2.me/theorems/add46db7-8b69-4745-9af2-5fac3c69ba88
-- title:
--   Wd3: ins mul
-- statement:
--   The Wd3 construction uses the ins mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L47-L53

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

theorem Formalism.FourierDecayAlt.P.Wd3.ins_mul (a : S) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) :
    ins a N * m = ∑ r, ∑ s, eU a r s * (N r s * m) := by sorry
