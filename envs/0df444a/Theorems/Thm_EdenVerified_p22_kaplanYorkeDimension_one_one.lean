-- Prove2me | Theorems.Thm_EdenVerified_p22_kaplanYorkeDimension_one_one
-- name    : EdenVerified.p22_kaplanYorkeDimension_one_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:50.267924+00:00
-- url     : https://prove2.me/theorems/8f9f923f-cbf2-462a-94fb-4c427285f028
-- title:
--   Eden Verified: p22 kaplan Yorke Dimension one one
-- statement:
--   The Eden Verified construction uses the p22 kaplan Yorke Dimension one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1775-L1778
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1775-L1778

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_kaplanYorkeDimension_one_one :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![2, 2, 0, 0, -c] = targetDimension c := by sorry
