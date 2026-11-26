-- Prove2me | Theorems.Thm_EdenVerified_p02_one_lt_squaredRadiusEvolution_iff
-- name    : EdenVerified.p02_one_lt_squaredRadiusEvolution_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:28:52.426445+00:00
-- url     : https://prove2.me/theorems/60514cae-262a-5b8a-8e51-9a4c1b25104a
-- title:
--   Eden Verified: p02 one lt squared Radius Evolution iff
-- statement:
--   The Eden Verified construction uses the p02 one lt squared Radius Evolution iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L778-L781
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L778-L781

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p02_one_lt_squaredRadiusEvolution_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    1 < squaredRadiusEvolution t s ↔ 1 < s := by sorry
