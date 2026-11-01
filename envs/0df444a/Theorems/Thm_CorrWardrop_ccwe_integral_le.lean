-- Prove2me | Theorems.Thm_CorrWardrop_ccwe_integral_le
-- name    : CorrWardrop.ccwe_integral_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:23.802156+00:00
-- url     : https://prove2.me/theorems/20d22655-5b6f-4f38-b782-cc822e62f5b0
-- title:
--   Proof of Proposition 4, pp.18–19 — every CCWE $\mu$ has $\int\Phi\,d\mu\le\Phi(z)$ for all $z\in\mathcal Y$
-- statement:
--   Let $\Gamma$ be a nonatomic game with a convex potential $\Phi$ (as in Lemma 3), and let $\mu$ be a coarse correlated Wardrop equilibrium of $\Gamma$. Then for every flow profile $z\in\mathcal Y$,
--   $$
--   \int\Phi(y)\,d\mu(y)\ \le\ \Phi(z).
--   $$
--   The paper argues by contradiction: if $\Phi(z)<\int\Phi\,d\mu$ for some $z$, integrating the gradient inequality produces a population $k$ and an action $b$ violating (4.3). Together with (4.11) this shows that every CCWE is a distribution over minimizers of $\Phi$, i.e. over WE.
--
--   Differences from the source:
--   - reading: "has a convex potential" (Definition 5: Φ C¹ on an open neighbourhood Ŷ of Y) → HasConvexPotential Γ Φ, i.e. Φ C¹ and convex on some open convex U ⊇ Y with ∂Φ/∂y^k_a = c^k_a on Y; reason: literal reading of "Φ convex" on its domain; any open neighbourhood of the compact convex Y contains an open convex one
--   - encoding: if Φ(z) < ∫Φ dμ for some z ∈ Y, then μ cannot be a CCWE → μ ∈ CCWE Γ → ∀ z ∈ Y, ∫Φ dμ ≤ Φ z; reason: contrapositive of the paragraph's claim; logically equivalent
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, proof of Proposition 4, paragraph "Conversely, take a CCWE µ …", pp.18–19

import Mathlib
import Definitions.Def_CorrWardrop_Model

open MeasureTheory

namespace CorrWardrop

/-- Proof of Proposition 4, first part: with a convex potential `Φ`, every CCWE `μ` satisfies
`∫ Φ(y) dμ(y) ≤ Φ(z)` for every `z ∈ Y` (the page shows that `Φ(z) < ∫ Φ(y) dμ(y)` for some
`z ∈ Y` contradicts (4.3), "so `μ` cannot be a CCWE").

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, pp.18–19. -/
theorem ccwe_integral_le {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
    [DecidableEq K] [∀ k, DecidableEq (A k)]
    (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (hΦ : HasConvexPotential Γ Φ)
    (μ : ProbabilityMeasure Γ.Y) (hμ : μ ∈ CCWE Γ) (z : Γ.Y) :
    ∫ y : Γ.Y, Φ (y : Flow A) ∂(μ : Measure Γ.Y) ≤ Φ z := by sorry

end CorrWardrop
