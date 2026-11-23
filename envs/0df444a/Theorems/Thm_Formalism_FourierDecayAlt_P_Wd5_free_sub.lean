-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_sub
-- name    : Formalism.FourierDecayAlt.P.Wd5.free_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:44.24735+00:00
-- url     : https://prove2.me/theorems/23173b9d-4652-4361-8efb-abe5ca79de7f
-- title:
--   Wd5: free sub
-- statement:
--   The Wd5 construction uses the free sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferMatrixFactorization.lean#L61-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferMatrixFactorization.lean#L61-L61

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

theorem Formalism.FourierDecayAlt.P.Wd5.free_sub {c : S} {b b' : SlopeTestRemainingChoices S A} (h : FreeOf c b) (h' : FreeOf c b') : FreeOf c (b - b') := by sorry
