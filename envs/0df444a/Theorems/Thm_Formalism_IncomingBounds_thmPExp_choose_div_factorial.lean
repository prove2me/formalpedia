-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_thmPExp_choose_div_factorial
-- name    : Formalism.IncomingBounds.thmPExp_choose_div_factorial
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:31:38.038822+00:00
-- url     : https://prove2.me/theorems/5b1e01d4-b4d6-4e3a-ba3a-118bc1e1b2a9
-- title:
--   Incoming Bounds: thm PExp choose div factorial
-- statement:
--   The Incoming Bounds construction uses the thm PExp choose div factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L49-L58

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
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
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds

theorem Formalism.IncomingBounds.thmPExp_choose_div_factorial {K : Type} [Field K] [CharZero K] {k j : ℕ} (hjk : j ≤ k) :
    ((k.choose j : ℕ) : K) / (k.factorial : K) =
      1 / ((j.factorial : K) * ((k - j).factorial : K)) := by sorry
