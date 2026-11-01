-- Prove2me | Theorems.Thm_DivQuotient_theorem_2
-- name    : DivQuotient.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:37.199812+00:00
-- url     : https://prove2.me/theorems/af7fd23a-d87b-4d4a-8afb-b6735e088ee2
-- title:
--   Theorem 2 — for $n\ge4$ and non-linear coherent $\phi$, seven axioms characterize DQ based on coherent risk measures
-- statement:
--   Let $n\ge4$ and let $\phi:\mathcal X\to\mathbb R$ be a non-linear coherent risk measure on $\mathcal X=L^\infty$. A diversification index $D:\mathcal X^n\to\overline{\mathbb R}$ satisfies
--
--   1. [+] non-negativity, [LI] location invariance, [SI] scale invariance,
--   2. [R]$_\phi$ rationality, [N]$_\phi$ normalization, [C]$_\phi$ continuity, and
--   3. [PC] portfolio convexity
--
--   if and only if
--
--   $$
--   D=\mathrm{DQ}^\rho_\alpha
--   $$
--
--   for some $\bar\alpha\in(0,\infty]$, some $\alpha\in I=(0,\bar\alpha)$ and some decreasing class $\rho=(\rho_\beta)_{\beta\in I}$ of (real-valued) coherent risk measures with $\rho_\alpha=\phi$.
--
--   This is the central result of the paper: seven economically motivated axioms single out the diversification quotients built on coherent risk measures, such as the family of Expected Shortfalls.
--
--   **Formalization Note** [C]$_\phi$ is the printed axiom. The probability space is arbitrary (the paper assumes it atomless, which the proof does not use).
--
--   Differences from the source:
--   - reading: (D(X) − D(Yᵏ))₊ in [C]φ, undefined on the page when D(X) = D(Yᵏ) = ∞ → max (D X − D Yᵏ) 0 in EReal, where ⊤ − ⊤ = ⊥, so the value is 0; reason: any other value makes [C]φ fail for every index taking the value ∞; it never arises on the DQ side, where D ≤ 1
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
--   - encoding: α* = inf{β ∈ I : …} with inf ∅ = ᾱ, ᾱ ∈ (0, ∞], DQ = α*/α, and a class (ρ_β)_{β∈I} → EReal infimum capped by ᾱ (min ᾱ (⨅ …)), divided in EReal by the real α > 0, and a map ℝ → Lp ℝ ⊤ P → … coerced to EReal; reason: the cap changes the value only on the empty set, where it gives ᾱ, and members outside I are never read; same values
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, Theorem 2, p.10; proof pp.36–37

import Mathlib
import Definitions.Def_DivQuotient_DQ

open MeasureTheory

namespace DivQuotient

/-- **Theorem 2** (Han–Lin–Wang, arXiv:2206.13679v6, p.10): "Suppose n ⩾ 4 and φ is a
non-linear coherent risk measure. A diversification index D : 𝒳ⁿ → ℝ̄ satisfies [+], [LI],
[SI], [R]φ, [N]φ, [C]φ and [PC] if and only if D is DQ^ρ_α for some α and decreasing class ρ of
coherent risk measures with ρ_α = φ."

**Formalization Note.** `𝒳 = L∞` is `Lp ℝ ⊤ P` over an arbitrary probability space (the
paper's atomlessness is not used). [C]φ is the printed axiom `AxC`. The class `ρ` consists of
real-valued risk measures indexed by `I = (0, ᾱ)`, `ᾱ ∈ (0, ∞]`, and enters `DQ` through its
coercion to `ℝ̄`; `DQ` uses the convention `inf ∅ = ᾱ`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 4 ≤ n) (φ : Lp ℝ ⊤ P → ℝ) (hφ : IsCoherent φ) (hnl : ¬ IsLinear φ)
    (D : (Fin n → Lp ℝ ⊤ P) → EReal) :
    (AxNonneg D ∧ AxLI D ∧ AxSI D ∧ AxR φ D ∧ AxN φ D ∧ AxC φ D ∧ AxPC D) ↔
      ∃ (abar : EReal) (ρ : ℝ → Lp ℝ ⊤ P → ℝ) (α : ℝ),
        α ∈ IndexSet abar ∧ (∀ β ∈ IndexSet abar, IsCoherent (ρ β)) ∧
          IsDecreasingClass abar (fun β X => (ρ β X : EReal)) ∧ ρ α = φ ∧
          D = DQ abar (fun β X => (ρ β X : EReal)) α := by sorry

end DivQuotient
