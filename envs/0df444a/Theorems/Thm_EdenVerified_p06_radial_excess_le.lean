-- Prove2me | Theorems.Thm_EdenVerified_p06_radial_excess_le
-- name    : EdenVerified.p06_radial_excess_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:31:31.775214+00:00
-- url     : https://prove2.me/theorems/942e80c4-b30d-5505-83b7-061d994d81b9
-- title:
--   Eden Verified: p06 radial excess le
-- statement:
--   The Eden Verified construction uses the p06 radial excess le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L906-L910
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L906-L910

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p06_radial_excess_le :
    ∀ {t r M : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hrM : r ≤ M) (hM : Real.sqrt 2 ≤ M),
    max (radiusEvolution t r - Real.sqrt 2) 0 ≤ radiusEvolution t M - Real.sqrt 2 := by sorry
