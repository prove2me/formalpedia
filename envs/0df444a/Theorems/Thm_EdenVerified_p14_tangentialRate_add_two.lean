-- Prove2me | Theorems.Thm_EdenVerified_p14_tangentialRate_add_two
-- name    : EdenVerified.p14_tangentialRate_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:36.419657+00:00
-- url     : https://prove2.me/theorems/8a779b2b-1461-53c4-ae4e-1cbb37f03562
-- title:
--   Eden Verified: p14 tangential Rate add two
-- statement:
--   The Eden Verified construction uses the p14 tangential Rate add two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1461-L1464
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1461-L1464

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p14_tangentialRate_add_two :
    ∀ (s : ℝ),
    tangentialRate s + 2 = s * (3 - s) := by sorry
