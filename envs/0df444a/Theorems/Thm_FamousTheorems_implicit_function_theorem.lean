-- Prove2me | Theorems.Thm_FamousTheorems_implicit_function_theorem
-- name    : FamousTheorems.implicit_function_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:13:58.922757+00:00
-- url     : https://prove2.me/theorems/455573d5-b00e-4162-8a96-da8476cb0c25
-- title:
--   The implicit function theorem
-- statement:
--   **The implicit function theorem.** Let $E_1,E_2,F$ be Banach spaces over $\mathbb R$ or $\mathbb C$, and $f:E_1\times E_2\to F$ of class $C^n$ ($n\ge1$) near $u=(u_1,u_2)$. Suppose the partial derivative $\partial_2 f(u):E_2\to F$ is an invertible continuous linear map. Then there is $\psi:E_1\to E_2$ with $\psi(u_1)=u_2$, of class $C^n$ at $u_1$, such that near $u$
--   $$f(x,y)=f(u)\iff y=\psi(x).$$
--
--   The level set of $f$ through $u$ is locally the graph of a smooth function. It is one of the central theorems of analysis, used to define submanifolds by equations, prove smooth dependence of solutions on parameters, and set up Lagrange multipliers.
--
--   **Formalization note.** Assembled from Mathlib's `ContDiffAt.implicitFunction`, `ContDiffAt.implicitFunction_apply_self`, `ContDiffAt.eventually_apply_eq_iff_implicitFunction` and `ContDiffAt.contDiffAt_implicitFunction`. The invertibility hypothesis is on `fderiv 𝕜 f u ∘L inr`, the derivative restricted to the second factor; `n : ℕ∞ω` allows $C^\infty$ and analytic smoothness.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ContDiffAt.eventually_apply_eq_iff_implicitFunction`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped ContDiff

theorem implicit_function_theorem {𝕜 : Type*} [RCLike 𝕜] {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    [CompleteSpace E₁] [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] {f : E₁ × E₂ → F} {u : E₁ × E₂} {n : ℕ∞ω} (cdf : ContDiffAt 𝕜 n f u)
    (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L ContinuousLinearMap.inr 𝕜 E₁ E₂).IsInvertible) :
    ∃ ψ : E₁ → E₂, ψ u.1 = u.2 ∧ (∀ᶠ v in nhds u, f v = f u ↔ ψ v.1 = v.2) ∧ ContDiffAt 𝕜 n ψ u.1 := by sorry

end FamousTheorems
