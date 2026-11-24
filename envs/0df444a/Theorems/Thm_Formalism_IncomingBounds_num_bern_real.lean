-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_num_bern_real
-- name    : Formalism.IncomingBounds.num_bern_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:54.64103+00:00
-- url     : https://prove2.me/theorems/eb32b57b-3357-452a-946d-bcb180a44eff
-- title:
--   Incoming Bounds: num bern real
-- statement:
--   The Incoming Bounds construction uses the num bern real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L213-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L213-L215

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

theorem Formalism.IncomingBounds.num_bern_real (a : ℝ) (ha : 1 ≤ a) (w : ℕ) : 1 + (w : ℝ) * (a - 1) ≤ a ^ w := by sorry
