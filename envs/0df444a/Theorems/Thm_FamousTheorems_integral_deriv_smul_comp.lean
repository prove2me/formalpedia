-- Prove2me | Theorems.Thm_FamousTheorems_integral_deriv_smul_comp
-- name    : FamousTheorems.integral_deriv_smul_comp
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:08.518296+00:00
-- url     : https://prove2.me/theorems/d5c2e129-e5e1-49a2-850a-acc887f7c028
-- title:
--   Integration by substitution
-- statement:
--   **Integration by substitution** (change of variables). For a differentiable $f$ and suitable $g$, $$\int_a^b g'(f(x))\cdot f'(x)\,dx = \int_{f(a)}^{f(b)} g'(u)\,du.$$ This is the chain rule integrated. Unlike integration by parts it does not simplify the integrand so much as change the coordinate in which it is read, and the factor $f'(x)$ is exactly the Jacobian of that change — which is why the several-variable version carries $|\det Df|$ and why the one-dimensional version needs no absolute value, the orientation being absorbed into the limits of integration. It is the most-used technique in elementary integration and, in its measure-theoretic form, the statement that pushing forward a measure and changing variables agree. **Formalization note.** The `smul` form covers vector-valued integrands, with the scalar derivative acting on values in a normed space. The result is Mathlib's `intervalIntegral.integral_deriv_smul_comp`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem integral_deriv_smul_comp :
    ∀ {a b : ℝ} {E : Type u_1} [inst : NormedAddCommGroup E] 
    [inst_1 : NormedSpace ℝ E] {f f' : ℝ → ℝ} {g : ℝ → E}, 
    (∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) → 
    ContinuousOn f' (uIcc a b) → Continuous g → ∫ (x : ℝ) in a..b, f' x • (g ∘ f) x = ∫ (x : ℝ) in f a..f b, g x := by sorry

end FamousTheorems
