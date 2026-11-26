-- Prove2me | Theorems.Thm_EdenVerified_s11_first_circle_in_plane
-- name    : EdenVerified.s11_first_circle_in_plane
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:24:55.092427+00:00
-- url     : https://prove2.me/theorems/3666bab9-5bbc-5b06-805d-bf90ecf48ec6
-- title:
--   Eden Verified: s11 first circle in plane
-- statement:
--   The first circle's perturbations lie in its own coordinate plane and in A.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L432-L436
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L432-L436

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s11_first_circle_in_plane (c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor ∩ coordinatePlane 0, Metric.infDist p (firstCircle 1) < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) (firstCircle 1) := by sorry
