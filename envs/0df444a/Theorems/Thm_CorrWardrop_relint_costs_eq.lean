-- Prove2me | Theorems.Thm_CorrWardrop_relint_costs_eq
-- name    : CorrWardrop.relint_costs_eq
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:29:19.076104+00:00
-- url     : https://prove2.me/theorems/a27bb8bc-8bb6-4c45-8a29-9f3072fc65fd
-- title:
--   Proof of Proposition 4, p.20 — all points of the relative interior of $\mathrm{WE}(\Gamma)$ have the same costs
-- statement:
--   Let $\Gamma$ be a nonatomic game with a convex potential (as in Lemma 3). If $\hat y$ and $\bar y$ are flow profiles in the relative interior of $\mathrm{WE}(\Gamma)$, then they have the same costs:
--   $$
--   c^k_a(\hat y)=c^k_a(\bar y)\qquad\text{for every } k\in\mathcal K \text{ and every } a\in\mathcal A^k .
--   $$
--   By continuity of the costs this extends from the relative interior to all of $\mathrm{WE}(\Gamma)$, which is the cost clause of Proposition 4.
--
--   Differences from the source:
--   - reading: "has a convex potential" (Definition 5: Φ C¹ on an open neighbourhood Ŷ of Y) → HasConvexPotential Γ Φ, i.e. Φ C¹ and convex on some open convex U ⊇ Y with ∂Φ/∂y^k_a = c^k_a on Y; reason: literal reading of "Φ convex" on its domain; any open neighbourhood of the compact convex Y contains an open convex one
--   - reading: c^k_a(ŷ) = c^k_a(ȳ) for every a ∈ B^k, and all points in the relative interior of WE(Γ) have the same costs → c k a ŷ = c k a ȳ for every k and every a ∈ A^k; reason: "the same costs" is the whole cost profile, the reading also used for Proposition 4; it is true for every action by the exchange property
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, proof of Proposition 4, second paragraph of p.20

import Mathlib
import Definitions.Def_CorrWardrop_Model
import Definitions.Def_CorrWardrop_Lagrangian
open MeasureTheory

namespace CorrWardrop

/-- Proof of Proposition 4, equal costs on the relative interior: if `Γ` has a convex
potential, then any two flows `ŷ, ȳ` in the relative interior of `WE(Γ)` have the same costs:
`c^k_a(ŷ) = c^k_a(ȳ)` for every `k ∈ K` and every `a ∈ A^k`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, p.20.

Formalization Note: the page first concludes for `a ∈ B^k` and then that "all points in the
relative interior of WE(Γ) have the same costs"; the statement asserts the full cost profile
(every action). -/
theorem relint_costs_eq {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
    [DecidableEq K] [∀ k, DecidableEq (A k)]
    (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (hΦ : HasConvexPotential Γ Φ)
    (y₁ y₂ : Γ.Y) (h₁ : (y₁ : Flow A) ∈ relintWE Γ) (h₂ : (y₂ : Flow A) ∈ relintWE Γ) :
    ∀ k (a : A k), Γ.c k a y₁ = Γ.c k a y₂ := by sorry

end CorrWardrop
