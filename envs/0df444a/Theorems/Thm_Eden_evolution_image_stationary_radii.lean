-- Prove2me | Theorems.Thm_Eden_evolution_image_stationary_radii
-- name    : Eden.evolution_image_stationary_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:27.405511+00:00
-- url     : https://prove2.me/theorems/5027bf00-cfc0-4936-bbd3-26d10c2aeb33
-- title:
--   Eden: evolution image stationary radii
-- statement:
--   Strict invariance of the stationary-radius sets used in the instability
--   statements.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L128-L151
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L128-L151

import Definitions.Def_Eden_InstabilityGeometry
import Definitions.Def_Eden_NonlinearInstability
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.evolution_image_stationary_radii (c : ℝ) {t a b : ℝ} (ht : 0 ≤ t)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    evolution c t '' {p | radiusSq₁ p = a ∧ radiusSq₂ p = b ∧ p 4 = 0} =
      {p | radiusSq₁ p = a ∧ radiusSq₂ p = b ∧ p 4 = 0} := by sorry
