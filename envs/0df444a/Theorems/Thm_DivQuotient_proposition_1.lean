-- Prove2me | Theorems.Thm_DivQuotient_proposition_1
-- name    : DivQuotient.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:14.734284+00:00
-- url     : https://prove2.me/theorems/796d3049-486a-404a-acc2-f78a3b4307f0
-- title:
--   Proposition 1 — DQ of a sub-linear class satisfies [PC], and its range is $[0,1]$
-- statement:
--   Let $\rho=(\rho_\beta)_{\beta\in I}$ be a decreasing class of real-valued sub-linear risk measures, $I=(0,\bar\alpha)$, and $\alpha\in I$.
--
--   1. $\mathrm{DQ}^\rho_\alpha$ satisfies [PC].
--   2. If $n\ge3$, $\rho_\alpha$ is non-linear, and there exists $X\in\mathcal X$ such that $\beta\mapsto\rho_\beta(X)$ is strictly decreasing on $I$, then
--   $$
--   \{\mathrm{DQ}^\rho_\alpha(\mathbf X):\mathbf X\in\mathcal X^n\}=[0,1].
--   $$
--
--   So the “if” direction of Theorem 2 needs neither [M] nor [CA] for the class, and under mild conditions DQ is a non-degenerate index with values filling $[0,1]$.
--
--   Differences from the source:
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
--   - encoding: α* = inf{β ∈ I : …} with inf ∅ = ᾱ, ᾱ ∈ (0, ∞], DQ = α*/α, and a class (ρ_β)_{β∈I} → EReal infimum capped by ᾱ (min ᾱ (⨅ …)), divided in EReal by the real α > 0, and a map ℝ → Lp ℝ ⊤ P → … coerced to EReal; reason: the cap changes the value only on the empty set, where it gives ᾱ, and members outside I are never read; same values
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, Proposition 1, p.11; proof p.44

import Mathlib
import Definitions.Def_DivQuotient_DQ

open MeasureTheory

namespace DivQuotient

/-- **Proposition 1** (Han–Lin–Wang, arXiv:2206.13679v6, p.11): "Let ρ = (ρ_β)_{β∈I} be a
decreasing class of sub-linear risk measures and α ∈ I. Then DQ^ρ_α satisfies [PC]. If n ⩾ 3,
ρ_α is non-linear and there exists X ∈ 𝒳 such that β ↦ ρ_β(X) is strictly decreasing, then
{DQ^ρ_α(X) : X ∈ 𝒳ⁿ} = [0, 1]."

**Formalization Note.** The risk measures are real valued (p.4); the class enters `DQ` through
its coercion to `ℝ̄`. "Strictly decreasing" is `StrictAntiOn` on `I`. The range is taken in
`ℝ̄`. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (abar : EReal) (ρ : ℝ → Lp ℝ ⊤ P → ℝ) (α : ℝ) (hα : α ∈ IndexSet abar)
    (hρ : ∀ β ∈ IndexSet abar, IsSublinear (ρ β))
    (hdec : IsDecreasingClass abar (fun β X => (ρ β X : EReal))) :
    AxPC (DQ (n := n) abar (fun β X => (ρ β X : EReal)) α) ∧
      (3 ≤ n → ¬ IsLinear (ρ α) →
        (∃ X : Lp ℝ ⊤ P, StrictAntiOn (fun β => ρ β X) (IndexSet abar)) →
        Set.range (DQ (n := n) abar (fun β X => (ρ β X : EReal)) α) = Set.Icc (0 : EReal) 1) := by sorry

end DivQuotient
