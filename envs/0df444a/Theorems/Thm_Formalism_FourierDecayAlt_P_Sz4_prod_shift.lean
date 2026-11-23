-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_shift
-- name    : Formalism.FourierDecayAlt.P.Sz4.prod_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:59.136451+00:00
-- url     : https://prove2.me/theorems/4bf46732-6857-4b8f-bf14-25a41f0f9881
-- title:
--   Sz4: prod shift
-- statement:
--   The Sz4 construction uses the prod shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L252-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L252-L258

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

theorem Formalism.FourierDecayAlt.P.Sz4.prod_shift (p : ℕ) (f : ℕ → ℝ) : ∏ i ∈ Icc 1 p, f (i + 1) = ∏ i ∈ Icc 2 (p + 1), f i := by sorry
