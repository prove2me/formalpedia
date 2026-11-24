-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_prod_range_eq_factorial_mul_prod_Ico
-- name    : Formalism.IncomingBounds.prod_range_eq_factorial_mul_prod_Ico
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:50.624256+00:00
-- url     : https://prove2.me/theorems/b150a752-825f-4803-8357-aedaee965d25
-- title:
--   Incoming Bounds: prod range eq factorial mul prod Ico
-- statement:
--   The Incoming Bounds construction uses the prod range eq factorial mul prod Ico property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L143-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L143-L152

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

theorem Formalism.IncomingBounds.prod_range_eq_factorial_mul_prod_Ico (m x : ℕ) :
    ∏ j ∈ Finset.range m, ((((m + 1) * x : ℕ) : ℚ) + j + 1) =
      (m.factorial : ℚ) * ∏ i ∈ Finset.Ico 1 (m + 1), (1 + ((m + 1 : ℕ) : ℚ) * (x : ℚ) / (i : ℚ)) := by sorry
