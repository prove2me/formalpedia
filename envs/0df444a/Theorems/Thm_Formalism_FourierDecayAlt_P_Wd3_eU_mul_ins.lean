-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_eU_mul_ins
-- name    : Formalism.FourierDecayAlt.P.Wd3.eU_mul_ins
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:00.250806+00:00
-- url     : https://prove2.me/theorems/d89e7693-7de3-4f64-a258-50227120886a
-- title:
--   Wd3: e U mul ins
-- statement:
--   The Wd3 construction uses the e U mul ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L55-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L55-L66

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

theorem Formalism.FourierDecayAlt.P.Wd3.eU_mul_ins (a : S) (k i : Fin 2) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m) :
    eU a k i * m * ins a N = ∑ s, eU a k s * (m * N i s) := by sorry
