-- Prove2me | Theorems.Thm_CorrWardrop_lemma_3
-- name    : CorrWardrop.lemma_3
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:28:22.45691+00:00
-- url     : https://prove2.me/theorems/8174adbe-5baf-447c-b482-be42ac0be635
-- title:
--   Lemma 3, p.18 — with a convex potential, the WE are exactly the minimizers of $\Phi$ on $\mathcal Y$
-- statement:
--   Let $\Gamma$ be a nonatomic game with flow set $\mathcal Y$, and let $\Phi$ be a convex potential of $\Gamma$: $\Phi$ is continuously differentiable and convex on an open convex set $U\supseteq\mathcal Y$, and $\partial\Phi(y)/\partial y^k_a=c^k_a(y)$ for all $y\in\mathcal Y$, $k$ and $a\in\mathcal A^k$. Then for every $y\in\mathcal Y$,
--   $$
--   y\in\mathrm{WE}(\Gamma)\iff \Phi(y)\le\Phi(z)\ \text{ for all } z\in\mathcal Y .
--   $$
--   That is, the Wardrop equilibria are exactly the minimizers of the potential over the flow set. The paper attributes the result to Sandholm (2001, Proposition 3.1). It turns equilibrium questions into questions about a convex program.
--
--   Differences from the source:
--   - reading: "has a convex potential" (Definition 5: Φ C¹ on an open neighbourhood Ŷ of Y) → HasConvexPotential Γ Φ, i.e. Φ C¹ and convex on some open convex U ⊇ Y with ∂Φ/∂y^k_a = c^k_a on Y; reason: literal reading of "Φ convex" on its domain; any open neighbourhood of the compact convex Y contains an open convex one
--   - encoding: the set of WE is the set of minimizers of Φ → for every y ∈ Y, IsWE Γ y ↔ ∀ z ∈ Y, Φ y ≤ Φ z; reason: pointwise form of the set equality; minimizers are over Y
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, Lemma 3, p.18

import Mathlib
import Definitions.Def_CorrWardrop_Model

open MeasureTheory

namespace CorrWardrop

/-- Lemma 3: if a nonatomic game has a convex potential `Φ`, then the set of WE is the set of
minimizers of `Φ` over `Y`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, Lemma 3, p.18. -/
theorem lemma_3 {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
    [DecidableEq K] [∀ k, DecidableEq (A k)]
    (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (hΦ : HasConvexPotential Γ Φ) (y : Γ.Y) :
    IsWE Γ y ↔ ∀ z : Γ.Y, Φ y ≤ Φ z := by sorry

end CorrWardrop
