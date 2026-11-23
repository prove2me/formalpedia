-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_freeOf2_one
-- name    : Formalism.FourierDecayAlt.P.Wd5.freeOf2_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:05.117176+00:00
-- url     : https://prove2.me/theorems/0bfeced5-d6cd-4bb2-baff-ed3fc19543ac
-- title:
--   Wd5: free Of2 one
-- statement:
--   The Wd5 construction uses the free Of2 one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferMatrixFactorization.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferMatrixFactorization.lean#L78-L83

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd5
open Matrix Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd5.freeOf2_one (c : S) : FreeOf2 c (1 : M2 (SlopeTestRemainingChoices S A)) := by sorry
