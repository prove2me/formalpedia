-- Prove2me | Theorems.Thm_EdenVerified_p02_squaredRadiusEvolution_lt_two_iff
-- name    : EdenVerified.p02_squaredRadiusEvolution_lt_two_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:28:56.340529+00:00
-- url     : https://prove2.me/theorems/f9a418d9-559a-52c9-978f-4033381b564b
-- title:
--   Eden Verified: p02 squared Radius Evolution lt two iff
-- statement:
--   The Eden Verified construction uses the p02 squared Radius Evolution lt two iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L783-L786
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L783-L786

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p02_squaredRadiusEvolution_lt_two_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    squaredRadiusEvolution t s < 2 ↔ s < 2 := by sorry
