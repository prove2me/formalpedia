-- Prove2me | Theorems.Thm_Eden_bounded_set_radius_bounds
-- name    : Eden.bounded_set_radius_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:41.717276+00:00
-- url     : https://prove2.me/theorems/bff8612a-255a-5cff-ae1f-b4d1b5af512c
-- title:
--   Eden: bounded set radius bounds
-- statement:
--   The Eden construction uses the bounded set radius bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L94-L104
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L94-L104

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.bounded_set_radius_bounds {B : Set PhaseSpace} (hB : Bornology.IsBounded B) :
    ∃ M W : ℝ, Real.sqrt 2 < M ∧ 0 ≤ W ∧ ∀ p ∈ B,
      Real.sqrt (radiusSq₁ p) ≤ M ∧ Real.sqrt (radiusSq₂ p) ≤ M ∧ |p 4| ≤ W := by sorry
