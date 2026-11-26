-- Prove2me | Theorems.Thm_EdenVerified_p02_two_lt_squaredRadiusEvolution_iff
-- name    : EdenVerified.p02_two_lt_squaredRadiusEvolution_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:29:11.036502+00:00
-- url     : https://prove2.me/theorems/ca1bdf40-717f-5d83-a4a0-4d6f4e5e26d8
-- title:
--   Eden Verified: p02 two lt squared Radius Evolution iff
-- statement:
--   The Eden Verified construction uses the p02 two lt squared Radius Evolution iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L788-L791
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L788-L791

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p02_two_lt_squaredRadiusEvolution_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    2 < squaredRadiusEvolution t s ↔ 2 < s := by sorry
