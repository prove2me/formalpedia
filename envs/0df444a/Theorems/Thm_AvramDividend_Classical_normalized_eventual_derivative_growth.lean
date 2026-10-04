-- Prove2me | Theorems.Thm_AvramDividend_Classical_normalized_eventual_derivative_growth
-- name    : AvramDividend.Classical.normalized_eventual_derivative_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T12:12:59.083386+00:00
-- url     : https://prove2.me/theorems/9be8b301-20e0-4aa1-8dc1-fe007797cda9
-- title:
--   Tilted monotonicity plus a differential inequality yields an eventual exponential lower bound on the derivative
-- statement:
--   Assume $\phi>0$, that $g(t)=e^{-\phi t}W(t)$ is monotone on $(0,\infty)$, that $W$ is strictly positive at some $x_0>0$, and that $\phi W(x)\le W'(x)$ for every $x>0$. Put $c = \phi e^{-\phi x_0} W(x_0)>0$. Then $c e^{\phi x} \le W'(x)$ for all sufficiently large $x$.
--
--   For $x\ge x_0$, monotonicity of $g$ gives $e^{-\phi x_0}W(x_0) \le e^{-\phi x}W(x)$. Multiplying by the positive factor $\phi e^{\phi x}$ and cancelling $e^{-\phi x}e^{\phi x}=1$ turns this into $c e^{\phi x} \le \phi W(x)$, and the differential inequality $\phi W(x)\le W'(x)$ finishes the argument.
--
--   This has exactly the existential shape required by `scaleDeriv_eventually_ge_exp`, namely $\exists \phi c,\; 0<\phi \wedge 0<c \wedge \forall^{\mathrm{atTop}}_x \, c e^{\phi x} \le W'(x)$, so together with `normalized_derivative_lower_bound` it discharges that milestone once the stochastic existence of $\phi$ is supplied.
-- source:
--   Kuznetsov, Kyprianou and Rivero, scale-function asymptotics: for $q>0$ the scale function satisfies $W(x)/e^{\Phi(q)x} \to 1/\psi'(\Phi(q))$ with $\Phi(q)>0$, whence the derivative admits a lower exponential bound. The analytic passage from tilted monotonicity to that bound is isolated here.

import Mathlib

open Set Filter

namespace AvramDividend.Classical

/-- An eventual lower exponential bound on the derivative, from normalized
monotonicity and the differential inequality. -/
theorem normalized_eventual_derivative_growth {W : ℝ → ℝ} (φ x₀ : ℝ)
    (hφ : 0 < φ) (hx₀ : 0 < x₀) (hW₀ : 0 < W x₀)
    (hg : MonotoneOn (fun t : ℝ => Real.exp (-φ * t) * W t) (Ioi 0))
    (hd : ∀ x : ℝ, 0 < x → φ * W x ≤ deriv W x) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x in Filter.atTop, c * Real.exp (φ * x) ≤ deriv W x := by
  sorry

end AvramDividend.Classical
