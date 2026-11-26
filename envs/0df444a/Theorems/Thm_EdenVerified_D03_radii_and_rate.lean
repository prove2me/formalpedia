-- Prove2me | Theorems.Thm_EdenVerified_D03_radii_and_rate
-- name    : EdenVerified.D03_radii_and_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:25:45.381835+00:00
-- url     : https://prove2.me/theorems/238400fb-50fe-501d-a359-143fb4471c8a
-- title:
--   Eden Verified: D03 radii and rate
-- statement:
--   Real coordinates, complex moduli and ordinary radii agree.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L505-L527
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L505-L527

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D03_radii_and_rate (p : PhaseSpace) :
    (radiusSq₁ p = p 0 ^ 2 + p 1 ^ 2) ∧
    (radiusSq₂ p = p 2 ^ 2 + p 3 ^ 2) ∧
    0 ≤ radiusSq₁ p ∧ 0 ≤ radiusSq₂ p ∧
    (‖(⟨p 0, p 1⟩ : ℂ)‖ ^ 2 = radiusSq₁ p) ∧
    (‖(⟨p 2, p 3⟩ : ℂ)‖ ^ 2 = radiusSq₂ p) ∧
    (‖(⟨p 0, p 1⟩ : ℂ)‖ = Real.sqrt (radiusSq₁ p)) ∧
    (‖(⟨p 2, p 3⟩ : ℂ)‖ = Real.sqrt (radiusSq₂ p)) ∧
    0 ≤ Real.sqrt (radiusSq₁ p) ∧ 0 ≤ Real.sqrt (radiusSq₂ p) ∧
    (∀ s : ℝ, q s = -(s - 1) * (s - 2) ∧ q s = -s ^ 2 + 3 * s - 2) ∧
    0 < Real.sqrt 2 := by sorry
