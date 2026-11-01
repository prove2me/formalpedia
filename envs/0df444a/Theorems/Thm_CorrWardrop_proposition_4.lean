-- Prove2me | Theorems.Thm_CorrWardrop_proposition_4
-- name    : CorrWardrop.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:31.847589+00:00
-- url     : https://prove2.me/theorems/0bc46d0a-d453-4548-ba2b-b853ca6885d5
-- title:
--   Proposition 4, p.18 — with a convex potential, $\mathrm{CCWE}(\Gamma)=\mathrm{CWE}(\Gamma)=\Delta(\mathrm{WE}(\Gamma))$ and all equilibria have the same cost profile
-- statement:
--   Let $\Gamma=(\mathcal K,\gamma,\mathcal A,c)$ be a nonatomic game: finitely many populations $k$ of sizes $\gamma^k>0$, finite action sets $\mathcal A^k$, flow set $\mathcal Y=\prod_k\Delta_{\gamma^k}(\mathcal A^k)$ and continuous costs $c^k_a:\mathcal Y\to\mathbb R$. Suppose $\Gamma$ has a convex potential $\Phi$: $\Phi$ is continuously differentiable and convex on an open convex set $U\supseteq\mathcal Y$, and $\partial\Phi(y)/\partial y^k_a=c^k_a(y)$ for all $y\in\mathcal Y$, $k$ and $a\in\mathcal A^k$. Then
--   $$
--   \mathrm{CCWE}(\Gamma)=\mathrm{CWE}(\Gamma)=\Delta(\mathrm{WE}(\Gamma)).\tag{4.10}
--   $$
--   In addition, all equilibria have the same cost profile:
--
--   1. if $y$ and $z$ are Wardrop equilibria, then $c^k_a(y)=c^k_a(z)$ for every $k\in\mathcal K$ and every $a\in\mathcal A^k$;
--   2. if $\mu$ is a coarse correlated Wardrop equilibrium (in particular, a correlated one) and $y_0$ is a Wardrop equilibrium, then $c^k_a(y)=c^k_a(y_0)$ for all $k,a$, for $\mu$-almost every $y$.
--
--   So in games with a convex potential, such as congestion games with nondecreasing costs, mediation cannot induce any outcome other than a mixture of Wardrop equilibria, and equilibrium costs are unique. Without a convex potential the first equality fails (El Farol game, Example 1 of the paper).
--
--   **Formalization Note.** $\Phi$ is a function on the whole flow space; only its values on $U$ matter. Neither $\mathcal K$ nor the $\mathcal A^k$ is assumed nonempty, and $\Phi$ is only convex, not strictly convex, so Wardrop equilibria need not be unique.
--
--   Differences from the source:
--   - reading: "has a convex potential" (Definition 5: Φ C¹ on an open neighbourhood Ŷ of Y) → HasConvexPotential Γ Φ, i.e. Φ C¹ and convex on some open convex U ⊇ Y with ∂Φ/∂y^k_a = c^k_a on Y; reason: literal reading of "Φ convex" on its domain; any open neighbourhood of the compact convex Y contains an open convex one; convexity on Y alone makes the cost clause false (Φ(y) = (y_a + y_b − 1) y_a, c_a = c_b = y_a, WE (1, 0) and (½, ½))
--   - reading: "all WE have the same costs profiles: all actions with positive flow have the same cost in all equilibria" → for all WE y, z, c k a y = c k a z for every k and every a ∈ A^k; reason: the cost profile is the whole vector (c^k_a)_{k,a}; this is the stronger of the two phrasings and it is true (the exchange step of the proof gives it for every action)
--   - reading: "(and therefore all CCWE and CWE)" have the same cost profiles → for every CCWE μ and every WE y₀, μ-almost every y has c k a y = c k a y₀ for all k, a; reason: a CCWE is a random flow; its cost profile is the WE one almost surely. Every CWE is a CCWE, so this covers CWE too
--   - encoding: Δ(Y) Borel probability distributions on Y; Δ(WE(Γ)) distributions over WE; ∂Φ(y)/∂y^k_a → ProbabilityMeasure on the subtype Y; a.e. condition "μ-almost every flow is a WE"; fderiv ℝ Φ y applied to the unit vector e^k_a; reason: WE(Γ) is closed, so the a.e. condition equals μ(WE(Γ)) = 1; Φ is C¹ on the open U ⊇ Y; same instances
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, Proposition 4, eq. (4.10), p.18 (proof pp.18–20)

import Mathlib
import Definitions.Def_CorrWardrop_Model

open MeasureTheory

namespace CorrWardrop

/-- Proposition 4: if a nonatomic game `Γ` has a convex potential, then
`CCWE(Γ) = CWE(Γ) = Δ(WE(Γ))` (4.10). In addition, all WE (and therefore all CCWE and CWE) have
the same cost profiles: for any two WE `y, z`, `c^k_a(y) = c^k_a(z)` for every `k ∈ K` and every
`a ∈ A^k`; and for every CCWE `μ` and every WE `y₀`, `μ`-almost every flow `y` has
`c^k_a(y) = c^k_a(y₀)` for all `k, a`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, Proposition 4, (4.10), p.18.

Formalization Note: "convex potential" is `HasConvexPotential` (Definition 5 with `Φ` convex on
an open convex neighbourhood of `Y`). "The same costs profiles" is read as equality of the whole
cost vector `(c^k_a)_{k, a}`, which is stronger than the gloss "all actions with positive flow
have the same cost". "Therefore all CCWE and CWE" is the last clause; every CWE is a CCWE. -/
theorem proposition_4 {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
    [DecidableEq K] [∀ k, DecidableEq (A k)]
    (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (hΦ : HasConvexPotential Γ Φ) :
    CCWE Γ = CWE Γ ∧ CWE Γ = DeltaWE Γ ∧
    (∀ y z : Γ.Y, IsWE Γ y → IsWE Γ z → ∀ k (a : A k), Γ.c k a y = Γ.c k a z) ∧
    ∀ μ ∈ CCWE Γ, ∀ y₀ : Γ.Y, IsWE Γ y₀ →
      ∀ᵐ y ∂(μ : Measure Γ.Y), ∀ k (a : A k), Γ.c k a y = Γ.c k a y₀ := by sorry

end CorrWardrop
