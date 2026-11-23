-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_sum_inv_sq_le_sub
-- name    : Formalism.FourierDecayAlt.P.Sz4.sum_inv_sq_le_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:43.904902+00:00
-- url     : https://prove2.me/theorems/34f8a78e-7b75-4bd4-ba7a-c6662a999dd9
-- title:
--   Sz4: sum inv sq le sub
-- statement:
--   The Sz4 construction uses the sum inv sq le sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L70-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L70-L82

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

theorem Formalism.FourierDecayAlt.P.Sz4.sum_inv_sq_le_sub (n : ℕ) (hn : 2 ≤ n) : ∑ d ∈ Ioc 0 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 7 / 4 - 1 / n := by sorry
