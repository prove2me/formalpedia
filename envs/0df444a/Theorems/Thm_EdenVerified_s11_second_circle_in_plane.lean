-- Prove2me | Theorems.Thm_EdenVerified_s11_second_circle_in_plane
-- name    : EdenVerified.s11_second_circle_in_plane
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:25:04.517426+00:00
-- url     : https://prove2.me/theorems/c5ab53c7-a445-5936-9116-2b089669f73e
-- title:
--   Eden Verified: s11 second circle in plane
-- statement:
--   The second circle's perturbations lie in its own coordinate plane and in A.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L439-L443
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L439-L443

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s11_second_circle_in_plane (c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor ∩ coordinatePlane 1, Metric.infDist p (secondCircle 1) < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) (secondCircle 1) := by sorry
