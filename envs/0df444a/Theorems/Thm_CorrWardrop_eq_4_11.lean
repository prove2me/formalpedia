-- Prove2me | Theorems.Thm_CorrWardrop_eq_4_11
-- name    : CorrWardrop.eq_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:22.043599+00:00
-- url     : https://prove2.me/theorems/26f73229-5659-4f05-b856-1e701a8bfdbd
-- title:
--   (4.11), p.18 — $\Delta(\arg\min\Phi)=\arg\min_{\mu\in\Delta(\mathcal Y)}E_\mu[\Phi]\subseteq\mathrm{CWE}(\Gamma)$
-- statement:
--   Let $\Gamma$ be a nonatomic game with a convex potential $\Phi$ (as in Lemma 3). Then
--   $$
--   \Delta(\arg\min\Phi)=\arg\min_{\mu\in\Delta(\mathcal Y)}E_\mu[\Phi]\subseteq\mathrm{CWE}(\Gamma).
--   $$
--   Precisely:
--
--   1. a probability distribution $\mu$ on $\mathcal Y$ is concentrated on the minimizers of $\Phi$ over $\mathcal Y$ if and only if $\int\Phi\,d\mu\le\int\Phi\,d\nu$ for every probability distribution $\nu$ on $\mathcal Y$;
--   2. every probability distribution on $\mathcal Y$ concentrated on the minimizers of $\Phi$ is a correlated Wardrop equilibrium.
--
--   This is the first step of the proof of Proposition 4: it gives the inclusion $\Delta(\mathrm{WE}(\Gamma))\subseteq\mathrm{CWE}(\Gamma)$ in the form needed later, and identifies distributions over WE with minimizers of the expected potential.
--
--   **Formalization Note.** $\Phi$ is continuous on the compact set $\mathcal Y$, so $\int\Phi\,d\mu$ is a genuine integral for every $\mu$.
--
--   Differences from the source:
--   - reading: "has a convex potential" (Definition 5: Φ C¹ on an open neighbourhood Ŷ of Y) → HasConvexPotential Γ Φ, i.e. Φ C¹ and convex on some open convex U ⊇ Y with ∂Φ/∂y^k_a = c^k_a on Y; reason: literal reading of "Φ convex" on its domain; any open neighbourhood of the compact convex Y contains an open convex one
--   - encoding: Δ(arg min Φ) = arg min_{μ∈Δ(Y)} E_μ[Φ] ⊆ CWE(Γ) → two clauses — for every μ, (μ-a.e. y minimizes Φ on Y) ↔ (∫Φ dμ ≤ ∫Φ dν for all ν); and every μ concentrated on the minimizers is a CWE; reason: set equality written pointwise, Δ(·) as an a.e. condition; same content
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, proof of Proposition 4, eq. (4.11), p.18

import Mathlib
import Definitions.Def_CorrWardrop_Model

open MeasureTheory

namespace CorrWardrop

/-- (4.11): with a convex potential `Φ`,
`Δ(arg min Φ) = arg min_{μ ∈ Δ(Y)} E_μ[Φ] ⊆ CWE(Γ)`.
(i) A distribution `μ` on `Y` is concentrated on the minimizers of `Φ` over `Y` if and only if
it minimizes `E_μ[Φ] = ∫ Φ dμ` over all distributions on `Y`; (ii) every distribution
concentrated on the minimizers of `Φ` is a CWE.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, (4.11), p.18.

Formalization Note: `Φ` is continuous on the compact set `Y`, so `y ↦ Φ(y)` is bounded and
integrable for every `μ`. -/
theorem eq_4_11 {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
    [DecidableEq K] [∀ k, DecidableEq (A k)]
    (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (hΦ : HasConvexPotential Γ Φ) :
    (∀ μ : ProbabilityMeasure Γ.Y,
      (∀ᵐ y : Γ.Y ∂(μ : Measure Γ.Y), ∀ z : Γ.Y, Φ (y : Flow A) ≤ Φ (z : Flow A)) ↔
        ∀ ν : ProbabilityMeasure Γ.Y,
          ∫ y : Γ.Y, Φ (y : Flow A) ∂(μ : Measure Γ.Y) ≤
            ∫ y : Γ.Y, Φ (y : Flow A) ∂(ν : Measure Γ.Y)) ∧
    ∀ μ : ProbabilityMeasure Γ.Y,
      (∀ᵐ y : Γ.Y ∂(μ : Measure Γ.Y), ∀ z : Γ.Y, Φ (y : Flow A) ≤ Φ (z : Flow A)) →
        μ ∈ CWE Γ := by sorry

end CorrWardrop
