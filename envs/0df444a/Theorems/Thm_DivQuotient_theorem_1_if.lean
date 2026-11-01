-- Prove2me | Theorems.Thm_DivQuotient_theorem_1_if
-- name    : DivQuotient.theorem_1_if
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:12.263961+00:00
-- url     : https://prove2.me/theorems/01c69a6b-492e-4f91-9b6c-9a2511058e9a
-- title:
--   Theorem 1, “if” direction (corrected: [C]$_\phi$ in semi-continuous form) — DQ satisfies the six axioms
-- statement:
--   Let $n\ge1$, $\bar\alpha\in(0,\infty]$, $I=(0,\bar\alpha)$ and $\alpha\in I$. Let $\rho=(\rho_\beta)_{\beta\in I}$ be a decreasing class of extended MCP risk measures (values in $[-\infty,\infty)$) such that $\rho_\alpha=\phi$ is real valued. Then $D=\mathrm{DQ}^\rho_\alpha$ satisfies
--
--   1. [+], [LI], [SI];
--   2. [R]$_\phi$ and [N]$_\phi$;
--   3. [C]$_\phi$ in its semi-continuous form: if $\mathbf Y^k\overset{m}{\simeq}\mathbf X$ and $\|(S(\mathbf X)-S(\mathbf Y^k))_+\|_\infty\to0$, then $\liminf_k D(\mathbf Y^k)\ge D(\mathbf X)$.
--
--   This is the easy half of the characterization: every DQ built on MCP risk measures has the six properties. The “Moreover” clause of Theorem 1 ($\rho_\alpha=\phi$) is built into the hypothesis.
--
--   **Formalization Note** $\phi$ is MCP because $\rho_\alpha=\phi$ is a member of the class.
--
--   Differences from the source:
--   - correction: [C]φ as printed: (D(X) − D(Yᵏ))₊ → 0 → the semi-continuous form AxCLsc (liminf D(Yᵏ) ≥ D(X)); reason: the printed axiom fails for DQ with ᾱ = ∞ at D(X) = ∞: I = (0, ∞), ρ_β = VaR_{β/(1+β)}, α = 1, X = (U1_A, U1_{Aᶜ}), Yᵏ = ((U − 1/k)1_A, (U − 1/k)1_{Aᶜ}) give D(X) = ∞ and D(Yᵏ) = k − 1; the page calls [C]φ 'a special form of semi-continuity' (p.8)
--   - generalization: ρ a decreasing class of (real-valued) MCP risk measures → members other than ρ_α may take the value −∞ (IsExtMCP); ρ_α = φ real; reason: every real-valued MCP class is such a class; the extended class is needed for the 'only if' direction (correction C1 of Theorem 1)
--   - encoding: n is a fixed positive integer (Notation, p.4) → hypothesis 0 < n; reason: the paper's standing assumption; at n = 0 the statement fails or is vacuous
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
--   - encoding: α* = inf{β ∈ I : …} with inf ∅ = ᾱ, ᾱ ∈ (0, ∞], DQ = α*/α, and a class (ρ_β)_{β∈I} → EReal infimum capped by ᾱ (min ᾱ (⨅ …)), divided in EReal by the real α > 0, and a map ℝ → Lp ℝ ⊤ P → … coerced to EReal; reason: the cap changes the value only on the empty set, where it gives ᾱ, and members outside I are never read; same values
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, Theorem 1, p.10; proof of the “if” statement, p.33

import Mathlib
import Definitions.Def_DivQuotient_DQ

open MeasureTheory

namespace DivQuotient

/-- **Theorem 1, "if" direction (corrected)** (Han–Lin–Wang, arXiv:2206.13679v6, p.10; proof
p.33). Let `ᾱ ∈ ℝ̄`, `α ∈ I = (0, ᾱ)`, and let `ρ = (ρ_β)_{β∈I}` be a decreasing class of
MCP risk measures with values in `[−∞, ∞)` such that `ρ_α = φ` is real valued. Then
`DQ^ρ_α` satisfies [+], [LI], [SI], [R]φ, [N]φ and [C]φ in its semi-continuous form.

**Formalization Note.** Corrections C1 and C2 of the mission: members other than `ρ_α` may
take the value `−∞` (`IsExtMCP`), and [C]φ is `AxCLsc` (`liminf D(Yᵏ) ≥ D(X)`), since the
printed `(D(X) − D(Yᵏ))₊ → 0` fails for some DQ with `ᾱ = ∞` at `D(X) = ∞`. The number of
assets is positive (p.4, "a fixed positive integer"). That `φ` is MCP follows from
`ρ_α = φ`. -/
theorem theorem_1_if {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (φ : Lp ℝ ⊤ P → ℝ) (abar : EReal) (ρ : ℝ → Lp ℝ ⊤ P → EReal) (α : ℝ)
    (hα : α ∈ IndexSet abar) (hρ : ∀ β ∈ IndexSet abar, IsExtMCP (ρ β))
    (hdec : IsDecreasingClass abar ρ) (hρα : ρ α = fun X => (φ X : EReal)) :
    AxNonneg (DQ (n := n) abar ρ α) ∧ AxLI (DQ (n := n) abar ρ α) ∧
      AxSI (DQ (n := n) abar ρ α) ∧ AxR φ (DQ (n := n) abar ρ α) ∧
      AxN φ (DQ (n := n) abar ρ α) ∧ AxCLsc φ (DQ (n := n) abar ρ α) := by sorry

end DivQuotient
