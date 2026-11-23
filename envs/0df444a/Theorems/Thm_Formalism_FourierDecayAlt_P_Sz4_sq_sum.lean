-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_sq_sum
-- name    : Formalism.FourierDecayAlt.P.Sz4.sq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:25.124462+00:00
-- url     : https://prove2.me/theorems/9cae6464-f6ef-4337-9527-0d60d58d855b
-- title:
--   Sz4: sq sum
-- statement:
--   The Sz4 construction uses the sq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L84-L91

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz4.sq_sum (n : ℕ) : ∑ d ∈ Ioc 0 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 7 / 4 := by sorry
