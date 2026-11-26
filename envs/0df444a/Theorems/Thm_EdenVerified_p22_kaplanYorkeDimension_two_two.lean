-- Prove2me | Theorems.Thm_EdenVerified_p22_kaplanYorkeDimension_two_two
-- name    : EdenVerified.p22_kaplanYorkeDimension_two_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:19.348711+00:00
-- url     : https://prove2.me/theorems/97ca8cb2-46df-4eb0-a619-df213679c301
-- title:
--   Eden Verified: p22 kaplan Yorke Dimension two two
-- statement:
--   The Eden Verified construction uses the p22 kaplan Yorke Dimension two two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1785-L1788
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1785-L1788

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_kaplanYorkeDimension_two_two :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![0, 0, -4, -4, -c] = 2 := by sorry
