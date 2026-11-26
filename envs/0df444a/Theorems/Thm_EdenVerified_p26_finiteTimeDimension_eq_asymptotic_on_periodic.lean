-- Prove2me | Theorems.Thm_EdenVerified_p26_finiteTimeDimension_eq_asymptotic_on_periodic
-- name    : EdenVerified.p26_finiteTimeDimension_eq_asymptotic_on_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:37:39.019119+00:00
-- url     : https://prove2.me/theorems/b8069ccc-d1d9-4440-a87b-6aa623304b7d
-- title:
--   Eden Verified: p26 finite Time Dimension eq asymptotic on periodic
-- statement:
--   The Eden Verified construction uses the p26 finite Time Dimension eq asymptotic on periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1145-L1149
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1145-L1149

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p26_finiteTimeDimension_eq_asymptotic_on_periodic :
    ∀ {c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ periodicEquilibriumSet c),
    finiteTimeDimension c t p = asymptoticDimension c p := by sorry
