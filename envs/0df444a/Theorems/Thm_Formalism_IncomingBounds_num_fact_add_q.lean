-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_num_fact_add_q
-- name    : Formalism.IncomingBounds.num_fact_add_q
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:50.031343+00:00
-- url     : https://prove2.me/theorems/7ae10b74-ee57-4e45-a930-26f3f7820f46
-- title:
--   Incoming Bounds: num fact add q
-- statement:
--   The Incoming Bounds construction uses the num fact add q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L134-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L134-L141

import Definitions.Def_Formalism_IncomingBounds_LemmaMNumerics
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds

theorem Formalism.IncomingBounds.num_fact_add_q (a k : ℕ) :
    (((a + k).factorial : ℕ) : ℚ) = (a.factorial : ℚ) * ∏ j ∈ Finset.range k, ((a : ℚ) + j + 1) := by sorry
