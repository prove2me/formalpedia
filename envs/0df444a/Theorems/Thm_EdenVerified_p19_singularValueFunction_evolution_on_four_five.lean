-- Prove2me | Theorems.Thm_EdenVerified_p19_singularValueFunction_evolution_on_four_five
-- name    : EdenVerified.p19_singularValueFunction_evolution_on_four_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:38.729677+00:00
-- url     : https://prove2.me/theorems/2ad9be1e-3b58-43c3-a02c-3dd6304f91bf
-- title:
--   Eden Verified: p19 singular Value Function evolution on four five
-- statement:
--   The Eden Verified construction uses the p19 singular Value Function evolution on four five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1579-L1585
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1579-L1585

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p19_singularValueFunction_evolution_on_four_five :
    ∀ {c t d : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd₄ : 4 ≤ d) (hd₅ : d ≤ 5),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (4 * t - 6 * volumeDefect t p - c * t * (d - 4)) := by sorry
