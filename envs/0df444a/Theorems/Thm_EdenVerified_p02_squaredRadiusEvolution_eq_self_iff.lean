-- Prove2me | Theorems.Thm_EdenVerified_p02_squaredRadiusEvolution_eq_self_iff
-- name    : EdenVerified.p02_squaredRadiusEvolution_eq_self_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:29:13.731984+00:00
-- url     : https://prove2.me/theorems/fc2eed50-b28a-54ff-8eb8-f042087ae10e
-- title:
--   Eden Verified: p02 squared Radius Evolution eq self iff
-- statement:
--   The Eden Verified construction uses the p02 squared Radius Evolution eq self iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L793-L796
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L793-L796

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p02_squaredRadiusEvolution_eq_self_iff :
    ∀ {t s : ℝ} (ht : 0 < t),
    squaredRadiusEvolution t s = s ↔ s = 0 ∨ s = 1 ∨ s = 2 := by sorry
