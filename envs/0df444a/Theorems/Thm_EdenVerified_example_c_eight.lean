-- Prove2me | Theorems.Thm_EdenVerified_example_c_eight
-- name    : EdenVerified.example_c_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:19:56.004389+00:00
-- url     : https://prove2.me/theorems/9c296040-0b94-535e-8d3c-e798d0a04341
-- title:
--   Eden Verified: example c eight
-- statement:
--   The numerical example immediately following the main theorem.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L91-L98
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L91-L98

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.example_c_eight :
    globalLyapunovDimension 8 attractor = 9 / 2 ∧
    IsGreatest (asymptoticDimension 8 '' periodicEquilibriumSet 8) 3 ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension 8 t '' periodicEquilibriumSet 8) 3) := by sorry
