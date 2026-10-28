-- Prove2me | Theorems.Thm_D1Bound5_finite_closed_window_incompatible
-- name    : D1Bound5.finite_closed_window_incompatible
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:44.869035+00:00
-- url     : https://prove2.me/theorems/a35af856-4de1-4a79-b040-cdfa7ab437eb
-- title:
--   Exclusion of a closed interval by a strict two-term estimate
-- statement:
--   Let $C,D,Z,U,V,\varepsilon$ be real numbers with $C,Z,U,V>0$ and $0\le\varepsilon<1$. Suppose
--   $$(1-\varepsilon)CD\le Z^2\le(1+\varepsilon)CD,\qquad 1<\frac UZ+VZ.$$
--   Then $D$ cannot satisfy both bounds
--   $$\frac{4U^2}{C(1-\varepsilon)}\le D\le\frac1{4V^2C(1+\varepsilon)}.$$
--   Both endpoints are included in the exclusion.
-- source:
--   D1Bound5/FiniteClosedWindow.lean, D1Bound5.finite_closed_window_incompatible, lines 21-49; original file SHA-256 c76f227fdc7536f8fd4a58375a484ac2d5bdae3cf78c3ac5339546d0024182fc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic

theorem D1Bound5.finite_closed_window_incompatible
    (C D Z U V eps : ℝ) (hC : 0 < C) (hZ : 0 < Z)
    (hU : 0 < U) (hV : 0 < V) (heps : 0 ≤ eps) (heps1 : eps < 1)
    (hrootlo : (1-eps)*C*D ≤ Z^2) (hroothi : Z^2 ≤ (1+eps)*C*D)
    (hform : 1 < U/Z+V*Z)
    (hlower : 4*U^2/(C*(1-eps)) ≤ D)
    (hupper : D ≤ 1/(4*V^2*C*(1+eps))) : False := by sorry
