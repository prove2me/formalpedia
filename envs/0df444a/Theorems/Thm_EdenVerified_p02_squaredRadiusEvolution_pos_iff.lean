-- Prove2me | Theorems.Thm_EdenVerified_p02_squaredRadiusEvolution_pos_iff
-- name    : EdenVerified.p02_squaredRadiusEvolution_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:29:12.32706+00:00
-- url     : https://prove2.me/theorems/5a81eaa3-85c2-43b1-bf41-ef9d8998f64b
-- title:
--   Eden Verified: p02 squared Radius Evolution pos iff
-- statement:
--   The Eden Verified construction uses the p02 squared Radius Evolution pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L768-L771
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L768-L771

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p02_squaredRadiusEvolution_pos_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    0 < squaredRadiusEvolution t s ↔ 0 < s := by sorry
