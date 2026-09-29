-- Prove2me | Theorems.Thm_FamousTheorems_deriv_comp
-- name    : FamousTheorems.deriv_comp
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:48.646244+00:00
-- url     : https://prove2.me/theorems/931d5844-10df-4057-93a2-4add54088282
-- title:
--   The chain rule
-- statement:
--   **The chain rule.** If $h$ is differentiable at $x$ and $h_2$ is differentiable at $h(x)$, then $$(h_2 \circ h)'(x) = h_2'\bigl(h(x)\bigr)\cdot h'(x).$$ Rates of change compose by multiplication. The statement is the derivative version of the fact that the best linear approximation to a composite is the composite of the best linear approximations, which is why the general form in several variables is composition of Jacobians rather than a product of numbers. Both differentiability hypotheses are needed and at the right points — $h$ at $x$, but $h_2$ at $h(x)$, not at $x$. The rule is what makes differentiation algorithmic: together with the product and sum rules it reduces any elementary derivative to a finite computation, and run in reverse over a computation graph it is exactly backpropagation. **Formalization note.** The scalar fields for the inner and outer functions may differ, with `NormedAlgebra` relating them, so the statement covers real functions of a complex variable and similar mixed cases. The result is Mathlib's `deriv_comp`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem deriv_comp :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] (x : 𝕜) {𝕜' : Type u_2} 
    [inst_1 : NontriviallyNormedField 𝕜'] [inst_2 : NormedAlgebra 𝕜 𝕜'] {h : 𝕜 → 𝕜'} {h₂ : 𝕜' → 𝕜'}, 
    DifferentiableAt 𝕜' h₂ (h x) → DifferentiableAt 𝕜 h x → deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x := by sorry

end FamousTheorems
