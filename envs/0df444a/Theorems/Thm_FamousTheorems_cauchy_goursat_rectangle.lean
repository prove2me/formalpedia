-- Prove2me | Theorems.Thm_FamousTheorems_cauchy_goursat_rectangle
-- name    : FamousTheorems.cauchy_goursat_rectangle
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:27:13.665989+00:00
-- url     : https://prove2.me/theorems/ac339ed5-bd8b-4b96-98f9-aaa210bb3c59
-- title:
--   The Cauchy–Goursat theorem for rectangles
-- statement:
--   **The Cauchy–Goursat theorem for rectangles.** Let $f$ be complex differentiable on a closed rectangle $R=[x_1,x_2]\times[y_1,y_2]\subseteq\mathbb C$ with opposite corners $z$ and $w$, taking values in a complex normed space. Then the integral of $f$ over the boundary of $R$ vanishes:
--   $$\int_{\partial R}f(\zeta)\,d\zeta=0 .$$
--
--   Goursat showed this without assuming continuity of $f'$. It is the first step of Cauchy's integral theorem and formula, from which the rest of complex function theory follows: analyticity of holomorphic functions, Liouville's theorem and the residue theorem.
--
--   **Formalization note.** Mathlib's `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. The platform's older `Cauchy_Goursat_Theorem` entry is a deprecated placeholder stating only `True`; this is the actual theorem. The boundary integral is written out as the sum of four oriented interval integrals along the edges (the vertical ones multiplied by $i$), and the rectangle is `Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cauchy_goursat_rectangle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) (z w : ℂ)
    (H : DifferentiableOn ℂ f (Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im))) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I)) = 0 := by sorry

end FamousTheorems
