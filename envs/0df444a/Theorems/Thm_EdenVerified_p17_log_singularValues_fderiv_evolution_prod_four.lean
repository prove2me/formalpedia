-- Prove2me | Theorems.Thm_EdenVerified_p17_log_singularValues_fderiv_evolution_prod_four
-- name    : EdenVerified.p17_log_singularValues_fderiv_evolution_prod_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:28.936962+00:00
-- url     : https://prove2.me/theorems/8dc4f69c-ac3b-4763-af77-7d531790d3d4
-- title:
--   Eden Verified: p17 log singular Values fderiv evolution prod four
-- statement:
--   The Eden Verified construction uses the p17 log singular Values fderiv evolution prod four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1545-L1550
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1545-L1550

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p17_log_singularValues_fderiv_evolution_prod_four :
    ∀ {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor),
    Real.log (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      4 * t - 6 * volumeDefect t p := by sorry
