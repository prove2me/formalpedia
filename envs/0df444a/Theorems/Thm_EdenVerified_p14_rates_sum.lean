-- Prove2me | Theorems.Thm_EdenVerified_p14_rates_sum
-- name    : EdenVerified.p14_rates_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:41.10752+00:00
-- url     : https://prove2.me/theorems/15a61265-6b39-4d0c-a7f7-9991e9300d31
-- title:
--   Eden Verified: p14 rates sum
-- statement:
--   The Eden Verified construction uses the p14 rates sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1466-L1469
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1466-L1469

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p14_rates_sum :
    ∀ (s : ℝ),
    radialRate s + tangentialRate s = 2 - 6 * (s - 1) ^ 2 := by sorry
