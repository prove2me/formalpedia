-- Prove2me | Theorems.Thm_CorrWardrop_grad_ineq
-- name    : CorrWardrop.grad_ineq
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:29.375192+00:00
-- url     : https://prove2.me/theorems/0422f765-97b8-4f9c-ad84-ff97d4bb4e47
-- title:
--   Proof of Proposition 4, pp.18–19 — $\Phi(z)-\Phi(y)\ge\sum_k\sum_a(z^k_a-y^k_a)c^k_a(y)$ on $\mathcal Y$
-- statement:
--   Let $\Gamma$ be a nonatomic game with a convex potential $\Phi$ (as in Lemma 3). For all flow profiles $y,z\in\mathcal Y$,
--   $$
--   \Phi(z)-\Phi(y)\ \ge\ \nabla\Phi(y)(z-y)\ =\ \sum_{k\in\mathcal K}\sum_{a\in\mathcal A^k}(z^k_a-y^k_a)\,c^k_a(y).
--   $$
--   The inequality is the first-order characterization of convexity; the equality expresses the gradient of the potential through the costs. Integrated against a coarse correlated equilibrium, this inequality is what links (4.3) to the expected potential.
--
--   Differences from the source:
--   - reading: "has a convex potential" (Definition 5: Φ C¹ on an open neighbourhood Ŷ of Y) → HasConvexPotential Γ Φ, i.e. Φ C¹ and convex on some open convex U ⊇ Y with ∂Φ/∂y^k_a = c^k_a on Y; reason: literal reading of "Φ convex" on its domain; any open neighbourhood of the compact convex Y contains an open convex one
--   - encoding: Φ(z) − Φ(y) ≥ ∇Φ(y)(z − y) (p.18) and ∇Φ(y)(z − y) = Σ_k Σ_a (z^k_a − y^k_a) c^k_a(y) (p.19) → one inequality Σ_k Σ_a (z k a − y k a) · c k a y ≤ Φ z − Φ y for y, z ∈ Y; reason: the two displays are used together in the proof, with y and z in Y, where ∂Φ = c
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, proof of Proposition 4, "Φ(z) − Φ(y) ≥ ∇Φ(y)(z − y)", p.18, and the display "∇Φ(y)(z − y) = Σ_k Σ_a (z^k_a − y^k_a) c^k_a(y)", p.19

import Mathlib
import Definitions.Def_CorrWardrop_Model

open MeasureTheory

namespace CorrWardrop

/-- Proof of Proposition 4, the gradient inequality: with a convex potential `Φ`, for all flow
profiles `y, z ∈ Y`,
`Φ(z) − Φ(y) ≥ ∇Φ(y)(z − y) = ∑_{k ∈ K} ∑_{a ∈ A^k} (z^k_a − y^k_a) c^k_a(y)`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, pp.18–19.

Formalization Note: the identity `∇Φ(y)(z − y) = ∑ (z^k_a − y^k_a) c^k_a(y)` (p.19) and the
first-order convexity inequality (p.18) are combined into one inequality, stated for
`y, z ∈ Y`, where the partial derivatives of `Φ` are the costs. -/
theorem grad_ineq {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
    [DecidableEq K] [∀ k, DecidableEq (A k)]
    (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (hΦ : HasConvexPotential Γ Φ) (y z : Γ.Y) :
    ∑ k, ∑ a, ((z : Flow A) k a - (y : Flow A) k a) * Γ.c k a y ≤ Φ z - Φ y := by sorry

end CorrWardrop
