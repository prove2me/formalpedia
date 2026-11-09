-- Prove2me | Theorems.Thm_ChoresTIE197_Main_result_1
-- name    : ChoresTIE197.Main.result_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:20:25.165691+00:00
-- url     : https://prove2.me/theorems/72de5b41-c188-4a96-ad24-529d802b3c0a
-- title:
--   Result 1 — truthful ex-post 1.97-MMS for every n≥2
-- statement:
--   For every number $n\ge2$ of agents and every finite set $M$ of chores, there exists one complete payment-free randomized mechanism on all nonnegative additive reports that is truthful in expectation and ex-ante envy-free and satisfies
--   $$c_i(X_i)\le\frac{197}{100}\mu_i(c)\qquad\text{for every profile }c,\text{ every supported }X,\text{ and every agent }i.$$
--   The mechanism is chosen before all true costs, deviations and opponents' reports. Identically zero rows, empty chore sets and fewer chores than agents are included. The result asserts an incentive-compatible mechanism, rather than a separate fair lottery chosen for each profile. No runtime or equal-marginal clause is added to the headline.
--
--   Differences from the source:
--   - encoding: finite labelled agents and chores with complete ordered partitions and public tie breaking → Fin indices starting at zero, nonnegative real singleton tables, PMFs on owner maps, index ties; reason: every finite source instance and complete allocation is represented, including empty bundles
--   - encoding: Result 1 includes all nonnegative additive costs; internal algorithms use positive MMS → the theorem ranges over all nonnegative reports; a separately defined first-zero-reporter wrapper supplies the zero-type construction; reason: zero true costs, false-zero reports, fixed other zero reports and empty chores are all included in the incentive comparisons
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Result 1, printed p.3, PDF p.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Families

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

theorem result_1 (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ∃ F : Mechanism n m,
      TIEOn (fun _ => True) F ∧ EFOn (fun _ => True) F ∧
      MMSOn (fun _ => True) (197/100:ℝ) F := by sorry

end ChoresTIE197.Main
