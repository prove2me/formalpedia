-- Prove2me | Theorems.Thm_CorrWardrop_kkt_iff
-- name    : CorrWardrop.kkt_iff
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:28:59.243575+00:00
-- url     : https://prove2.me/theorems/4ffc0ef0-8a5b-437b-922e-31696acdc435
-- title:
--   Proof of Proposition 4, p.19 — $\hat y\in\mathcal Y$ minimizes $\Phi$ iff KKT multipliers $\hat\lambda$ exist
-- statement:
--   Let $\Gamma$ be a nonatomic game with a convex potential $\Phi$ (as in Lemma 3). For a flow profile $\hat y\in\mathcal Y$, the following are equivalent:
--
--   1. $\hat y$ is a solution of $\min\{\Phi(y): y\in\mathcal Y\}$;
--   2. there exist multipliers $\hat\lambda=\big((\hat\lambda^k)_k,(\hat\lambda^k_a)_{k,a}\big)$ such that for all $k\in\mathcal K$ and $a\in\mathcal A^k$
--   $$
--   \frac{\partial\Phi}{\partial y^k_a}(\hat y)=\hat\lambda^k+\hat\lambda^k_a,\qquad \hat\lambda^k_a\,\hat y^k_a=0,\qquad \hat\lambda^k_a\ge 0,\qquad \sum_{a\in\mathcal A^k}\hat y^k_a=\gamma^k .
--   $$
--
--   This is the KKT theorem for the convex program whose solutions are, by Lemma 3, the Wardrop equilibria. Through condition 2, the gradient of $\Phi$ at a WE is pinned down by the multipliers, which is how the proof shows that all WE have the same costs.
--
--   Differences from the source:
--   - reading: "has a convex potential" (Definition 5: Φ C¹ on an open neighbourhood Ŷ of Y) → HasConvexPotential Γ Φ, i.e. Φ C¹ and convex on some open convex U ⊇ Y with ∂Φ/∂y^k_a = c^k_a on Y; reason: literal reading of "Φ convex" on its domain; any open neighbourhood of the compact convex Y contains an open convex one
--   - reading: ŷ is a solution iff there exists λ̂ with (ŷ, λ̂) satisfying the KKT conditions (the printed list omits ŷ ≥ 0) → for ŷ ∈ Y (so ŷ ≥ 0), (∀ z ∈ Y, Φ ŷ ≤ Φ z) ↔ ∃ λ̂, KKT Γ Φ ŷ λ̂; reason: "ŷ is a solution" presupposes feasibility; without ŷ ≥ 0 the "if" direction is false (one population, A = {a, b}, γ = 1, Φ(y) = (y_a + y_b)², ŷ = (2, −1), λ̂^k = 2, λ̂_a = λ̂_b = 0 satisfies the printed list)
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, proof of Proposition 4, KKT conditions, p.19

import Mathlib
import Definitions.Def_CorrWardrop_Model
import Definitions.Def_CorrWardrop_Lagrangian
open MeasureTheory

namespace CorrWardrop

/-- Proof of Proposition 4, KKT theorem: with a convex potential `Φ`, a flow profile `ŷ ∈ Y` is a
solution of `min {Φ(y) : y ∈ Y}` if and only if there exist multipliers `λ̂` such that
`(ŷ, λ̂)` satisfies the KKT conditions.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, KKT conditions, p.19.

Formalization Note: `ŷ` ranges over `Y`, so primal feasibility `ŷ ≥ 0` is assumed ("`ŷ` is a
solution" presupposes it); the printed KKT list does not contain it. -/
theorem kkt_iff {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
    [DecidableEq K] [∀ k, DecidableEq (A k)]
    (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (hΦ : HasConvexPotential Γ Φ) (y : Γ.Y) :
    (∀ z : Γ.Y, Φ y ≤ Φ z) ↔ ∃ l : Multipliers A, KKT Γ Φ y l := by sorry

end CorrWardrop
