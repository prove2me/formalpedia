-- Prove2me | Theorems.Thm_EdenVerified_p06_bounded_set_radius_bounds
-- name    : EdenVerified.p06_bounded_set_radius_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:31:55.35518+00:00
-- url     : https://prove2.me/theorems/2b7c8ded-707e-4065-8e0a-f9bf1ff18889
-- title:
--   Eden Verified: p06 bounded set radius bounds
-- statement:
--   The Eden Verified construction uses the p06 bounded set radius bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L900-L904
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L900-L904

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p06_bounded_set_radius_bounds :
    ∀ {B : Set PhaseSpace} (hB : Bornology.IsBounded B),
    ∃ M W : ℝ, Real.sqrt 2 < M ∧ 0 ≤ W ∧ ∀ p ∈ B,
      Real.sqrt (radiusSq₁ p) ≤ M ∧ Real.sqrt (radiusSq₂ p) ≤ M ∧ |p 4| ≤ W := by sorry
