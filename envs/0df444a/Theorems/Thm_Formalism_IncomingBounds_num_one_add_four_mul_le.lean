-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_num_one_add_four_mul_le
-- name    : Formalism.IncomingBounds.num_one_add_four_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:38.020841+00:00
-- url     : https://prove2.me/theorems/d9c8e092-1ffc-483f-874a-5790077fa2e3
-- title:
--   Incoming Bounds: num one add four mul le
-- statement:
--   The Incoming Bounds construction uses the num one add four mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L177-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L177-L183

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

theorem Formalism.IncomingBounds.num_one_add_four_mul_le (v : ℕ) : 1 + 4 * v ≤ 5 ^ v := by sorry
