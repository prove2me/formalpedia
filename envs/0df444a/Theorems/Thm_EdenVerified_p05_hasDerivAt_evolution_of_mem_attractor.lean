-- Prove2me | Theorems.Thm_EdenVerified_p05_hasDerivAt_evolution_of_mem_attractor
-- name    : EdenVerified.p05_hasDerivAt_evolution_of_mem_attractor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:30:52.162911+00:00
-- url     : https://prove2.me/theorems/d5e658fe-2c0c-59b4-a5a9-15b4469f1f61
-- title:
--   Eden Verified: p05 has Deriv At evolution of mem attractor
-- statement:
--   The Eden Verified construction uses the p05 has Deriv At evolution of mem attractor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L871-L875
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L871-L875

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p05_hasDerivAt_evolution_of_mem_attractor :
    ∀ (c t : ℝ) {p : PhaseSpace}
    (hp : p ∈ attractor),
    HasDerivAt (fun τ => evolution c τ p) (vectorField c (evolution c t p)) t := by sorry
