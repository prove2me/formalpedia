-- Prove2me | Theorems.Thm_EdenVerified_p14_radialRate_add_four
-- name    : EdenVerified.p14_radialRate_add_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:28.384865+00:00
-- url     : https://prove2.me/theorems/a39249d0-7258-4aa6-8444-9ac8112c7cb7
-- title:
--   Eden Verified: p14 radial Rate add four
-- statement:
--   The Eden Verified construction uses the p14 radial Rate add four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1456-L1459
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1456-L1459

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p14_radialRate_add_four :
    ∀ (s : ℝ),
    radialRate s + 4 = (2 - s) * (5 * s + 1) := by sorry
