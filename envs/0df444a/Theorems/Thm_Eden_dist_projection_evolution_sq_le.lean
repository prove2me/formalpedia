-- Prove2me | Theorems.Thm_Eden_dist_projection_evolution_sq_le
-- name    : Eden.dist_projection_evolution_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:55.700889+00:00
-- url     : https://prove2.me/theorems/083c66ca-05fd-5a58-a06d-0b8c41542c18
-- title:
--   Eden: dist projection evolution sq le
-- statement:
--   The Eden construction uses the dist projection evolution sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L33-L56
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L33-L56

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.dist_projection_evolution_sq_le (c : ℝ) {M W t : ℝ} (ht : 0 ≤ t)
    (hM : Real.sqrt 2 ≤ M) {p : PhaseSpace}
    (h₁ : Real.sqrt (radiusSq₁ p) ≤ M) (h₂ : Real.sqrt (radiusSq₂ p) ≤ M)
    (hw : |p 4| ≤ W) :
    dist (evolution c t p) (attractorProjection (evolution c t p)) ^ 2 ≤
      attractionBound c M W t := by sorry
