-- Prove2me | Theorems.Thm_FamousTheorems_jacobi_discriminant_product_7b
-- name    : FamousTheorems.jacobi_discriminant_product_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:27.276984+00:00
-- url     : https://prove2.me/theorems/9604feb3-dc4f-4ee3-bdb7-45c83148a06b
-- title:
--   Jacobi's product formula Δ = q∏(1 − qⁿ)²⁴
-- statement:
--   **Jacobi's product formula for the discriminant.** For every $z$ in the upper half-plane, with $q=e^{2\pi iz}$,
--   $$\Delta(z)=q\prod_{n=1}^\infty(1-q^n)^{24}.$$
--
--   Equivalently $\Delta=\eta^{24}$, where $\eta$ is the Dedekind eta function. The $q$-expansion coefficients of $\Delta$ are the values $\tau(n)$ of Ramanujan's tau function, and the product formula is the starting point for Ramanujan's conjectures on $\tau$. Jacobi derived it from his triple product identity.
--
--   **Formalization note.** Mathlib's `ModularForm.discriminant_eq_q_prod`. `Function.Periodic.qParam 1 z` is $e^{2\pi iz}$, and `ModularForm.eta_q n z` is $q^{n+1}$, so the product runs over $n\ge0$ with factors $(1-q^{n+1})^{24}$. Here $\Delta$ is the modular form of weight $12$ built by Mathlib from this product.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ModularForm.discriminant_eq_q_prod`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jacobi_discriminant_product_7b (z : UpperHalfPlane) :
    ModularForm.discriminant z =
      Function.Periodic.qParam 1 (z : ℂ) * ∏' n : ℕ, (1 - ModularForm.eta_q n (z : ℂ)) ^ 24 := by sorry

end FamousTheorems
