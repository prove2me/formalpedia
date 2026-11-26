-- Prove2me | Theorems.Thm_Eden_planar_surjective_on_disc
-- name    : Eden.planar_surjective_on_disc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:15.8521+00:00
-- url     : https://prove2.me/theorems/06e2e8d9-0c54-4050-a894-0e8c6d5f347d
-- title:
--   Eden: planar surjective on disc
-- statement:
--   Every point of the closed disc has a preimage in that disc.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StrictInvariance.lean#L27-L60
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StrictInvariance.lean#L27-L60

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Eden_StrictInvariance
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planar_surjective_on_disc (Ω : ℝ) {t x y : ℝ} (ht : 0 ≤ t)
    (hxy : x ^ 2 + y ^ 2 ≤ 2) :
    ∃ u v : ℝ, u ^ 2 + v ^ 2 ≤ 2 ∧ planarX Ω t u v = x ∧ planarY Ω t u v = y := by sorry
