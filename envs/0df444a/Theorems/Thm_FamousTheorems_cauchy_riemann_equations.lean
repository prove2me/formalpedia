-- Prove2me | Theorems.Thm_FamousTheorems_cauchy_riemann_equations
-- name    : FamousTheorems.cauchy_riemann_equations
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:41.949871+00:00
-- url     : https://prove2.me/theorems/0d41b5fb-9d58-4cc8-bbcc-4b2353ccf7c8
-- title:
--   The Cauchy–Riemann equations
-- statement:
--   **The Cauchy–Riemann equations.** A function $f:\mathbb C\to E$ into a complex normed space is complex differentiable at $x$ if and only if it is real differentiable at $x$ and its real derivative $Df(x)$ satisfies
--   $$Df(x)(i)=i\cdot Df(x)(1),$$
--   that is, $\partial f/\partial y=i\,\partial f/\partial x$ at $x$.
--
--   For $f=u+iv$ this condition is the classical pair $u_x=v_y$, $u_y=-v_x$. It says that the real derivative is complex linear, and it is where the rigidity of holomorphic functions comes from.
--
--   **Formalization note.** Mathlib's `differentiableAt_complex_iff_differentiableAt_real`. `fderiv ℝ f x` is the real Fréchet derivative, a real-linear map $\mathbb C\to E$. Evaluating it at `1` and at `Complex.I` gives the partial derivatives in the $x$ and $y$ directions.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `differentiableAt_complex_iff_differentiableAt_real`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cauchy_riemann_equations {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {x : ℂ} :
    DifferentiableAt ℂ f x ↔
      DifferentiableAt ℝ f x ∧ fderiv ℝ f x Complex.I = Complex.I • fderiv ℝ f x 1 := by sorry

end FamousTheorems
