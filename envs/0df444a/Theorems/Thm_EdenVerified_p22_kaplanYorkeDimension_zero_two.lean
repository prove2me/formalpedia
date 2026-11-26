-- Prove2me | Theorems.Thm_EdenVerified_p22_kaplanYorkeDimension_zero_two
-- name    : EdenVerified.p22_kaplanYorkeDimension_zero_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:50:52.931055+00:00
-- url     : https://prove2.me/theorems/58075deb-f81e-5a64-b465-1247dc80c3b9
-- title:
--   Eden Verified: p22 kaplan Yorke Dimension zero two
-- statement:
--   The Eden Verified construction uses the p22 kaplan Yorke Dimension zero two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1770-L1773
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1770-L1773

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_kaplanYorkeDimension_zero_two :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![0, -2, -2, -4, -c] = 1 := by sorry
