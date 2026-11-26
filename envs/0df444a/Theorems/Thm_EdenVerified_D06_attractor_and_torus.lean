-- Prove2me | Theorems.Thm_EdenVerified_D06_attractor_and_torus
-- name    : EdenVerified.D06_attractor_and_torus
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:26:17.804342+00:00
-- url     : https://prove2.me/theorems/1a72c63c-8436-513c-a602-2600f3b20f7a
-- title:
--   Eden Verified: D06 attractor and torus
-- statement:
--   The squared-radius and ordinary-radius descriptions define the same sets.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L563-L577
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L563-L577

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D06_attractor_and_torus :
    attractor = {p : PhaseSpace | radiusSq₁ p ≤ 2 ∧ radiusSq₂ p ≤ 2 ∧ p 4 = 0} ∧
    torus = {p : PhaseSpace | radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 ∧ p 4 = 0} ∧
    attractor = {p : PhaseSpace | Real.sqrt (radiusSq₁ p) ≤ Real.sqrt 2 ∧
      Real.sqrt (radiusSq₂ p) ≤ Real.sqrt 2 ∧ p 4 = 0} ∧
    torus = {p : PhaseSpace | Real.sqrt (radiusSq₁ p) = 1 ∧
      Real.sqrt (radiusSq₂ p) = 1 ∧ p 4 = 0} ∧
    attractor.Nonempty ∧ IsCompact attractor ∧
    torus.Nonempty ∧ IsCompact torus ∧ torus ⊆ attractor := by sorry
