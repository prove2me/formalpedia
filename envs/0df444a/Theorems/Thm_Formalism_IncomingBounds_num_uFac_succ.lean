-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_num_uFac_succ
-- name    : Formalism.IncomingBounds.num_uFac_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:51.216797+00:00
-- url     : https://prove2.me/theorems/b8db9c59-383d-4b05-92b7-cd9a0b995c15
-- title:
--   Incoming Bounds: num u Fac succ
-- statement:
--   The Incoming Bounds construction uses the num u Fac succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L154-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L154-L165

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

theorem Formalism.IncomingBounds.num_uFac_succ (m x : ℕ) :
    uFac (m + 1) (x + 1) = uFac (m + 1) x * (-(m.factorial : ℚ) *
      ∏ i ∈ Finset.Ico 1 (m + 1), (1 + ((m + 1 : ℕ) : ℚ) * (x : ℚ) / (i : ℚ))) := by sorry
