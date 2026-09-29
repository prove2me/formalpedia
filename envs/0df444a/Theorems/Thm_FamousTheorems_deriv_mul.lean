-- Prove2me | Theorems.Thm_FamousTheorems_deriv_mul
-- name    : FamousTheorems.deriv_mul
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:06.860252+00:00
-- url     : https://prove2.me/theorems/175f8066-4728-4779-a0c3-1293c188de59
-- title:
--   The Leibniz product rule
-- statement:
--   **The product rule.** If $c$ and $d$ are differentiable at $x$ then $$(cd)'(x) = c'(x)\,d(x) + c(x)\,d'(x).$$ The derivative of a product is not the product of the derivatives; the correct formula has two terms, one for each factor being varied while the other is held fixed. That structure is what makes differentiation a *derivation* rather than a ring homomorphism, and the abstract notion of derivation in algebra takes exactly this identity as its defining axiom. Iterating gives the general Leibniz rule $(cd)^{(n)} = \sum_k \binom{n}{k} c^{(k)} d^{(n-k)}$, with binomial coefficients appearing for the same combinatorial reason as in the binomial theorem. Together with the sum and chain rules it makes differentiation of elementary expressions purely mechanical. **Formalization note.** The functions take values in a normed algebra over the base field, so the statement covers matrix- and operator-valued functions where multiplication is noncommutative — which is why the order of factors in each term matters. The result is Mathlib's `deriv_mul`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem deriv_mul :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {𝔸 : Type u_2} [inst_1 : NormedRing 𝔸] 
    [inst_2 : NormedAlgebra 𝕜 𝔸] {c d : 𝕜 → 𝔸}, 
    DifferentiableAt 𝕜 c x → DifferentiableAt 𝕜 d x → deriv (c * d) x = deriv c x * d x + c x * deriv d x := by sorry

end FamousTheorems
