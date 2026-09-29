-- Prove2me | Theorems.Thm_FamousTheorems_integral_mul_deriv_eq_deriv_mul
-- name    : FamousTheorems.integral_mul_deriv_eq_deriv_mul
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:07.541542+00:00
-- url     : https://prove2.me/theorems/6123b36d-9b2b-4ca4-b8aa-02d795c5b7c5
-- title:
--   Integration by parts
-- statement:
--   **Integration by parts.** For suitably differentiable $u, v$ on $[a,b]$, $$\int_a^b u(x)\,v'(x)\,dx = u(b)v(b) - u(a)v(a) - \int_a^b u'(x)\,v(x)\,dx.$$ This is the product rule integrated: the boundary term collects the total change in $uv$, and what remains trades a derivative from one factor to the other. That trade is the whole point — an integrand becomes tractable when the differentiation is moved onto the simpler factor. It is the source of reduction formulas for $\int x^n e^x$ and $\int \sin^n x$, of the Gamma function's functional equation $\Gamma(s+1) = s\Gamma(s)$, and of the definition of weak derivatives: distributions are defined so that integration by parts holds by fiat, which is what allows differential equations to be posed for non-differentiable functions. **Formalization note.** The hypotheses ask for `HasDerivAt` on the interior with interval-integrability of the derivatives. The result is Mathlib's `intervalIntegral.integral_mul_deriv_eq_deriv_mul`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem integral_mul_deriv_eq_deriv_mul :
    ∀ {a b : ℝ} {A : Type u_1} [inst : NormedRing A] 
    [inst_1 : NormedAlgebra ℝ A] [CompleteSpace A] {u v u' v' : ℝ → A}, 
    (∀ x ∈ uIcc a b, HasDerivAt u (u' x) x) → 
    (∀ x ∈ uIcc a b, HasDerivAt v (v' x) x) → 
    IntervalIntegrable u' MeasureTheory.volume a b → 
    IntervalIntegrable v' MeasureTheory.volume a b → 
    ∫ (x : ℝ) in a..b, u x * v' x = u b * v b - u a * v a - ∫ (x : ℝ) in a..b, u' x * v x := by sorry

end FamousTheorems
