-- Prove2me | Theorems.Thm_EdenVerified_p26_asymptoticDimension_first_outer_circle
-- name    : EdenVerified.p26_asymptoticDimension_first_outer_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:37:44.015385+00:00
-- url     : https://prove2.me/theorems/32d07a08-66a3-41a6-94d8-46e88c1c6fc8
-- title:
--   Eden Verified: p26 asymptotic Dimension first outer circle
-- statement:
--   The Eden Verified construction uses the p26 asymptotic Dimension first outer circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1163-L1167
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1163-L1167

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p26_asymptoticDimension_first_outer_circle :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 2),
    asymptoticDimension c p = 1 := by sorry
