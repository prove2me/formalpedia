-- Prove2me | Theorems.Thm_EdenVerified_p20_finiteTimeDimension_attractor_isGreatest
-- name    : EdenVerified.p20_finiteTimeDimension_attractor_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:01.736258+00:00
-- url     : https://prove2.me/theorems/feaf1bd8-ce5f-4b3c-9dca-33ae616b5079
-- title:
--   Eden Verified: p20 finite Time Dimension attractor is Greatest
-- statement:
--   The Eden Verified construction uses the p20 finite Time Dimension attractor is Greatest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1628-L1631
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1628-L1631

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p20_finiteTimeDimension_attractor_isGreatest :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t),
    IsGreatest (finiteTimeDimension c t '' attractor) (targetDimension c) := by sorry
