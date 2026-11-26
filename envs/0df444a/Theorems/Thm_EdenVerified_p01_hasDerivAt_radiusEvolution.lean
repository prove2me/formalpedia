-- Prove2me | Theorems.Thm_EdenVerified_p01_hasDerivAt_radiusEvolution
-- name    : EdenVerified.p01_hasDerivAt_radiusEvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:27:14.500737+00:00
-- url     : https://prove2.me/theorems/bcb88494-b0e5-5918-a10c-35e0f1eace98
-- title:
--   Eden Verified: p01 has Deriv At radius Evolution
-- statement:
--   The Eden Verified construction uses the p01 has Deriv At radius Evolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L699-L702
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L699-L702

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p01_hasDerivAt_radiusEvolution :
    ∀ {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r),
    HasDerivAt (fun τ => radiusEvolution τ r) (radialField (radiusEvolution t r)) t := by sorry
