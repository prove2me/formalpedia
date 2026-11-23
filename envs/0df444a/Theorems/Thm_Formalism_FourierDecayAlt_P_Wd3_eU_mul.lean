-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_eU_mul
-- name    : Formalism.FourierDecayAlt.P.Wd3.eU_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:59.763101+00:00
-- url     : https://prove2.me/theorems/f4bf4e6f-c394-428f-89aa-88695d25de8b
-- title:
--   Wd3: e U mul
-- statement:
--   The Wd3 construction uses the e U mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L12-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L12-L36

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

theorem Formalism.FourierDecayAlt.P.Wd3.eU_mul (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by sorry
