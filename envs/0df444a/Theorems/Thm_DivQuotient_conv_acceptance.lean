-- Prove2me | Theorems.Thm_DivQuotient_conv_acceptance
-- name    : DivQuotient.conv_acceptance
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:18.83038+00:00
-- url     : https://prove2.me/theorems/36ab373e-ed7b-43db-9614-400424fbbb5f
-- title:
--   Proof of Theorem 2 — $\mathrm{Conv}\{X-\phi(X)\}=\{\phi\le0\}$, with a common $\theta$
-- statement:
--   Let $\phi$ (the page's $\rho_\alpha$) be a non-linear coherent risk measure.
--
--   1. The convex hull of $\{X-\phi(X):X\in\mathcal X\}$ is $\{X\in\mathcal X:\phi(X)\le0\}$.
--   2. There is $Y_0\in\mathcal X$ with $\phi(Y_0)+\phi(-Y_0)>0$ such that, with $Y_1=1-Y_0$, every $Z$ with $\phi(Z)\le0$ satisfies, for all sufficiently large $\theta$,
--   $$
--   Z=(1-2\lambda)\big(X-\phi(X)\big)+\lambda\big(\theta Y_0-\phi(\theta Y_0)\big)+\lambda\big(\theta Y_1-\phi(\theta Y_1)\big)
--   $$
--   for some $\lambda\in[0,\tfrac12)$ and $X\in\mathcal X$.
--
--   Clause 2 is the three-point representation the proof builds; since it holds for all large $\theta$, one $\theta$ serves two positions at once, which is how two acceptable positions are written as portfolios of a single four-asset vector (hence $n\ge4$ in Theorem 2).
--
--   Differences from the source:
--   - generalization: Conv{X − ρ_α(X)} = {ρ_α ≤ 0} → the identity and the three-point form for all large θ; reason: the proof on pp.36–37 constructs this representation and uses it with a common θ for two points; dropping clause 2 gives the printed identity
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, proof of Theorem 2, pp.36–37

import Mathlib
import Definitions.Def_DivQuotient_RiskMeasure

open MeasureTheory Filter

namespace DivQuotient

/-- **Proof of Theorem 2, convex-hull identity** (Han–Lin–Wang, arXiv:2206.13679v6, pp.36–37):
"Next, we show that Conv{X − ρ_α(X) : X ∈ 𝒳} = {X ∈ 𝒳 : ρ_α(X) ⩽ 0}."

Let `φ` (the page's `ρ_α`) be a non-linear coherent risk measure. Then

1. `Conv{X − φ(X) : X ∈ 𝒳} = {X ∈ 𝒳 : φ(X) ≤ 0}`;
2. (the three-point form used on p.37) there is `Y₀` with `φ(Y₀) + φ(−Y₀) > 0` such that,
   with `Y₁ = 1 − Y₀`, every `Z` with `φ(Z) ≤ 0` satisfies, for all sufficiently large `θ`,
   `Z = (1 − 2λ)(X − φ(X)) + λ(θY₀ − φ(θY₀)) + λ(θY₁ − φ(θY₁))` for some `λ ∈ [0, 1/2)` and
   `X ∈ 𝒳`.

**Formalization Note.** Clause 2 makes explicit that one `θ` serves any finitely many `Z`,
which the proof on p.37 uses for two points at once. -/
theorem conv_acceptance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (φ : Lp ℝ ⊤ P → ℝ) (hφ : IsCoherent φ) (hnl : ¬ IsLinear φ) :
    convexHull ℝ (Set.range fun X : Lp ℝ ⊤ P => X - Lp.const ⊤ P (φ X)) = {X | φ X ≤ 0} ∧
      ∃ Y₀ : Lp ℝ ⊤ P, 0 < φ Y₀ + φ (-Y₀) ∧
        ∀ Z : Lp ℝ ⊤ P, φ Z ≤ 0 → ∀ᶠ θ : ℝ in atTop,
          ∃ l ∈ Set.Ico (0 : ℝ) (1 / 2), ∃ X : Lp ℝ ⊤ P,
            Z = (1 - 2 * l) • (X - Lp.const ⊤ P (φ X)) +
                l • (θ • Y₀ - Lp.const ⊤ P (φ (θ • Y₀))) +
                l • (θ • (Lp.const ⊤ P 1 - Y₀) - Lp.const ⊤ P (φ (θ • (Lp.const ⊤ P 1 - Y₀)))) := by sorry

end DivQuotient
