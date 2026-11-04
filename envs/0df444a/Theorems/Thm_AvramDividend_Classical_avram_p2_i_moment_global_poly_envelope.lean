-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_global_poly_envelope
-- name    : AvramDividend.Classical.avram_p2_i_moment_global_poly_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:21:30.623029+00:00
-- url     : https://prove2.me/theorems/dcf4ae78-d74e-4b21-9134-6728dd2520a8
-- title:
--   Global positive-half-line polynomial approximation error with a high-moment envelope
-- statement:
--   If a test g vanishes on z≥1, p approximates g to epsilon on [0,2], and |p(z)|≤epsilon z^K for z≥2, then |g(z)-p(z)|≤epsilon(1+z^K) on all z≥0. This removes the need to split the integral at z=2: the absolute integral error is dominated by a constant mass plus one high moment, while allowing the approximating measures to carry mass on z>1.

import Mathlib
open Set Filter Topology

theorem AvramDividend.Classical.avram_p2_i_moment_global_poly_envelope
    (g : ℝ → ℝ) (p : Polynomial ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (K : ℕ) (hg0 : ∀ z : ℝ, 1 ≤ z → g z = 0)
    (happrox : ∀ z ∈ Set.Icc (0 : ℝ) 2, |p.eval z - g z| ≤ ε)
    (htail : ∀ z : ℝ, 2 ≤ z → |p.eval z| ≤ ε * z ^ K) :
    ∀ z : ℝ, 0 ≤ z →
      |g z - p.eval z| ≤ ε * (1 + z ^ K) := by sorry
