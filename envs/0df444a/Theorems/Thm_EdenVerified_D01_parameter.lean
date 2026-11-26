-- Prove2me | Theorems.Thm_EdenVerified_D01_parameter
-- name    : EdenVerified.D01_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:26:16.998218+00:00
-- url     : https://prove2.me/theorems/2b388d0e-6b22-463a-8b49-150d6471b3b4
-- title:
--   Eden Verified: D01 parameter
-- statement:
--   The parameter range is c>4.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L491-L493
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L491-L493

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D01_parameter (c : ℝ) (hc : 4 < c) :
    0 < c ∧ 4 < 4 + 4 / c ∧ 4 + 4 / c < 5 := by sorry
