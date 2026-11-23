-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_eU_mul_ins
-- name    : Formalism.FourierDecayAlt.P.Wd2.eU_mul_ins
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:00.334039+00:00
-- url     : https://prove2.me/theorems/2fa5ace5-d5c3-495a-840a-8cc23922fb97
-- title:
--   Wd2: e U mul ins
-- statement:
--   The Wd2 construction uses the e U mul ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L95-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L95-L107

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

theorem Formalism.FourierDecayAlt.P.Wd2.eU_mul_ins (a : S) (m i : Fin 2) (N : M2 (SlopeTestRemainingChoices S A)) :
    eU a m i * ins a N = ∑ l, eU a m l * N i l := by sorry
