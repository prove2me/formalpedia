-- Prove2me | Theorems.Thm_EdenVerified_p20_finiteTimeDimension_eq_target_iff
-- name    : EdenVerified.p20_finiteTimeDimension_eq_target_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:22.674475+00:00
-- url     : https://prove2.me/theorems/69883b61-a516-5b5b-9539-15e1ab650182
-- title:
--   Eden Verified: p20 finite Time Dimension eq target iff
-- statement:
--   The Eden Verified construction uses the p20 finite Time Dimension eq target iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1622-L1626
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1622-L1626

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p20_finiteTimeDimension_eq_target_iff :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    finiteTimeDimension c t p = targetDimension c ↔ p ∈ torus := by sorry
