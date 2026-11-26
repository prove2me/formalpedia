-- Prove2me | Theorems.Thm_EdenVerified_p16_singularValues_fderiv_evolution_fifth
-- name    : EdenVerified.p16_singularValues_fderiv_evolution_fifth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:36.16481+00:00
-- url     : https://prove2.me/theorems/20eec37b-d725-5062-adc9-0a62804141b0
-- title:
--   Eden Verified: p16 singular Values fderiv evolution fifth
-- statement:
--   The Eden Verified construction uses the p16 singular Values fderiv evolution fifth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1514-L1518
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1514-L1518

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p16_singularValues_fderiv_evolution_fifth :
    ∀ {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    (fderiv ℝ (evolution c t) p).toLinearMap.singularValues 4 = Real.exp (-c * t) := by sorry
