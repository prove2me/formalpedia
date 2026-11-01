-- Prove2me | Theorems.Thm_DivQuotient_theorem_1
-- name    : DivQuotient.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:18.536182+00:00
-- url     : https://prove2.me/theorems/a78de9d9-4077-4dc1-9832-2807bd117877
-- title:
--   Theorem 1 (corrected: class members may be $-\infty$; [C]$_\phi$ semi-continuous) — six axioms characterize DQ based on MCP risk measures
-- statement:
--   Let $n\ge1$ and let $\phi$ be an MCP risk measure. A diversification index $D:\mathcal X^n\to\overline{\mathbb R}$ satisfies [+], [LI], [SI], [R]$_\phi$, [N]$_\phi$ and [C]$_\phi$ (in semi-continuous form) if and only if
--
--   $$
--   D=\mathrm{DQ}^\rho_\alpha
--   $$
--
--   for some $\bar\alpha\in(0,\infty]$, some $\alpha\in I=(0,\bar\alpha)$ and some decreasing class $\rho=(\rho_\beta)_{\beta\in I}$ of extended MCP risk measures (values in $[-\infty,\infty)$) with $\rho_\alpha=\phi$.
--
--   This is the first axiomatic characterization of diversification indices; the goal theorem (Theorem 2) adds portfolio convexity to it. Fixing $\phi$ on both sides is the paper's “Moreover, in both directions … it can be required that $\rho_\alpha=\phi$”.
--
--   Differences from the source:
--   - correction: ρ a decreasing class of (real-valued) MCP risk measures → members other than ρ_α may take the value −∞ (IsExtMCP: values in [−∞, ∞), [M], [CA], [PH] in EReal); ρ_α = φ real; reason: with real-valued members the clause ρ_α = φ of the 'only if' direction is false: n = 2, φ = VaR_{1/2} on an atomless space, D = min(1, DQ^{VaR}_{1/2}) satisfies the six axioms, but D = DQ^ρ_α with real MCP ρ_β, β > α, forces ρ_β(0) ≤ −2K < 0 = ρ_β(0)
--   - correction: [C]φ as printed: (D(X) − D(Yᵏ))₊ → 0 → the semi-continuous form AxCLsc (liminf D(Yᵏ) ≥ D(X)); reason: the printed axiom fails for DQ with ᾱ = ∞ at D(X) = ∞: I = (0, ∞), ρ_β = VaR_{β/(1+β)}, α = 1, X = (U1_A, U1_{Aᶜ}), Yᵏ = ((U − 1/k)1_A, (U − 1/k)1_{Aᶜ}) give D(X) = ∞ and D(Yᵏ) = k − 1; the page calls [C]φ 'a special form of semi-continuity' (p.8)
--   - generalization: D satisfies the axioms for some MCP φ iff D = DQ^ρ_α for some class; moreover one can require ρ_α = φ → for each fixed MCP φ: D satisfies the axioms for φ iff D = DQ^ρ_α for some class with ρ_α = φ; reason: the fixed-φ equivalence implies both the plain equivalence and the 'Moreover' clause
--   - encoding: n is a fixed positive integer (Notation, p.4) → hypothesis 0 < n; reason: the paper's standing assumption; at n = 0 the statement fails or is vacuous
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
--   - encoding: α* = inf{β ∈ I : …} with inf ∅ = ᾱ, ᾱ ∈ (0, ∞], DQ = α*/α, and a class (ρ_β)_{β∈I} → EReal infimum capped by ᾱ (min ᾱ (⨅ …)), divided in EReal by the real α > 0, and a map ℝ → Lp ℝ ⊤ P → … coerced to EReal; reason: the cap changes the value only on the empty set, where it gives ᾱ, and members outside I are never read; same values
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, Theorem 1, p.10; proof pp.33–35

import Mathlib
import Definitions.Def_DivQuotient_DQ

open MeasureTheory

namespace DivQuotient

/-- **Theorem 1 (corrected)** (Han–Lin–Wang, arXiv:2206.13679v6, p.10): "A diversification
index D : 𝒳ⁿ → ℝ̄ satisfies [+], [LI], [SI], [R]φ, [N]φ and [C]φ for some MCP risk measure φ if
and only if D is DQ^ρ_α for some α and decreasing class ρ of MCP risk measures. Moreover, in
both directions of the above equivalence, it can be required that ρ_α = φ."

For a fixed MCP `φ` and `n ≥ 1`: `D` satisfies [+], [LI], [SI], [R]φ, [N]φ and [C]φ (in
semi-continuous form) iff `D = DQ^ρ_α` for some `ᾱ`, `α ∈ (0, ᾱ)` and decreasing class `ρ`
of `[−∞, ∞)`-valued MCP risk measures with `ρ_α = φ`.

**Formalization Note.** Corrections C1 (the members other than `ρ_α` may take the value
`−∞`) and C2 ([C]φ read as `liminf D(Yᵏ) ≥ D(X)`). Fixing `φ` on both sides states the
"Moreover" form, which implies the plain equivalence. `n ≥ 1` is the paper's standing
assumption (p.4); at `n = 0` [N]φ cannot hold. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (φ : Lp ℝ ⊤ P → ℝ) (hφ : IsMCP φ) (D : (Fin n → Lp ℝ ⊤ P) → EReal) :
    (AxNonneg D ∧ AxLI D ∧ AxSI D ∧ AxR φ D ∧ AxN φ D ∧ AxCLsc φ D) ↔
      ∃ (abar : EReal) (ρ : ℝ → Lp ℝ ⊤ P → EReal) (α : ℝ),
        α ∈ IndexSet abar ∧ (∀ β ∈ IndexSet abar, IsExtMCP (ρ β)) ∧
          IsDecreasingClass abar ρ ∧ ρ α = (fun X => (φ X : EReal)) ∧ D = DQ abar ρ α := by sorry

end DivQuotient
