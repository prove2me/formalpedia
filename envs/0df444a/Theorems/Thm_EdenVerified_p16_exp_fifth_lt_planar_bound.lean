-- Prove2me | Theorems.Thm_EdenVerified_p16_exp_fifth_lt_planar_bound
-- name    : EdenVerified.p16_exp_fifth_lt_planar_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:23.733954+00:00
-- url     : https://prove2.me/theorems/364d979c-7bfc-5708-ae01-84b967d097c5
-- title:
--   Eden Verified: p16 exp fifth lt planar bound
-- statement:
--   The Eden Verified construction uses the p16 exp fifth lt planar bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1503-L1506
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1503-L1506

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p16_exp_fifth_lt_planar_bound :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t),
    Real.exp (-c * t) < Real.exp (-4 * t) := by sorry
