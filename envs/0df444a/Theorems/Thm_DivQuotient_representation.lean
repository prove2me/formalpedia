-- Prove2me | Theorems.Thm_DivQuotient_representation
-- name    : DivQuotient.representation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:06.670513+00:00
-- url     : https://prove2.me/theorems/e73397ff-0fbc-4e45-9071-c6fd4b8186fa
-- title:
--   Proof of Theorem 1, the representation (corrected: $\rho_\beta$ may be $-\infty$) — $D(\mathbf X)=\inf\{\beta>0:\rho_\beta(\sum X_i)\le\sum\phi(X_i)\}$
-- statement:
--   Throughout, $\phi$ is an MCP risk measure and $D:\mathcal X^n\to\overline{\mathbb R}$ satisfies [+], [LI], [SI], [R]$_\phi$, [N]$_\phi$ and the semi-continuous form of [C]$_\phi$ (the standing assumptions of the “only if” part of the proof of Theorem 1). $R$ is the map (EC.1), $\mathcal A_\beta=\{R\le\beta\}$ and $\rho_\beta(X)=\inf\{m\in\mathbb R:X-m\in\mathcal A_\beta\}$.
--
--   1. Each $\rho_\beta$, $\beta>0$, is an extended MCP risk measure: it never takes the value $+\infty$ and satisfies [M], [CA] and [PH].
--   2. $\rho_\beta$ is decreasing in $\beta$.
--   3. For every $\mathbf X\in\mathcal X^n$, with $I=(0,\infty)$ and $\inf\varnothing=\infty$,
--   $$
--   D(\mathbf X)=\inf\Big\{\beta\in I:\ \rho_\beta\Big(\sum_{i=1}^nX_i\Big)\le\sum_{i=1}^n\phi(X_i)\Big\}.
--   $$
--
--   This is the core of the “only if” direction: the index is recovered from a class of risk measures built from $D$ alone.
--
--   Differences from the source:
--   - correction: (ρ_β)_{β∈I} is a class of MCP risk measures → each ρ_β is an extended MCP risk measure (values in [−∞, ∞)); reason: ρ_β = inf{m : X − m ∈ 𝒜_β} is −∞ when 𝒜_β = 𝒳: for n = 2, φ = VaR_{1/2} on an atomless space and D = min(1, DQ^{VaR}_{1/2}), which satisfies the six axioms, R ≤ 1 everywhere, so ρ_β ≡ −∞ for β ≥ 1
--   - generalization: D satisfies the printed [C]φ: (D(X) − D(Yᵏ))₊ → 0 → D satisfies the semi-continuous form AxCLsc: d < D(X) implies eventually d < D(Yᵏ); reason: the printed axiom implies the semi-continuous one (proved in the mission's sanity file), so the statement specializes to the page's hypotheses
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, proof of Theorem 1, pp.34–35

import Mathlib
import Definitions.Def_DivQuotient_ProofObjects

open MeasureTheory

namespace DivQuotient

/-- **Proof of Theorem 1, the representation** (Han–Lin–Wang, arXiv:2206.13679v6, pp.34–35).
Let `φ` be MCP and let `D` satisfy [+], [LI], [SI], [R]φ, [N]φ and [C]φ (semi-continuous
form). With `I = (0, ∞)`, `𝒜_β = {R ≤ β}` and `ρ_β(X) = inf{m ∈ ℝ : X − m ∈ 𝒜_β}`:

1. each `ρ_β`, `β > 0`, is an MCP risk measure with values in `[−∞, ∞)`;
2. `ρ_β` is decreasing in `β`;
3. for all `X ∈ 𝒳ⁿ`, `D(X) = inf{β ∈ I : ρ_β(∑ Xᵢ) ⩽ ∑ φ(Xᵢ)}`, with `inf ∅ = ∞`.

**Formalization Note.** Correction C1: the page calls `(ρ_β)` "a class of MCP risk measures";
`ρ_β` can take the value `−∞`, so clause 1 is `IsExtMCP`. The infimum in clause 3 is the
`EReal` infimum, `⊤` on the empty set. -/
theorem representation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (φ : Lp ℝ ⊤ P → ℝ) (hφ : IsMCP φ) (D : (Fin n → Lp ℝ ⊤ P) → EReal)
    (hNonneg : AxNonneg D) (hLI : AxLI D) (hSI : AxSI D) (hR : AxR φ D) (hN : AxN φ D)
    (hC : AxCLsc φ D) :
    (∀ β : ℝ, 0 < β → IsExtMCP (rhoBeta φ D β)) ∧
      (∀ β γ : ℝ, 0 < β → β ≤ γ → ∀ X, rhoBeta φ D γ X ≤ rhoBeta φ D β X) ∧
      ∀ X : Fin n → Lp ℝ ⊤ P,
        D X = ⨅ β ∈ {β : ℝ | 0 < β ∧ rhoBeta φ D β (S X) ≤ ∑ i, (φ (X i) : EReal)},
          (β : EReal) := by sorry

end DivQuotient
