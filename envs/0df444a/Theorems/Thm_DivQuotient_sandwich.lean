-- Prove2me | Theorems.Thm_DivQuotient_sandwich
-- name    : DivQuotient.sandwich
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:02.573868+00:00
-- url     : https://prove2.me/theorems/2f724d5d-5644-47b6-8352-44a6c725f6d1
-- title:
--   Proof of Theorem 1, the sandwich $\rho_{1-\varepsilon}\ge\phi\ge\rho_{1+\varepsilon}$ (with an added clause for subadditive $\phi$)
-- statement:
--   Throughout, $\phi$ is an MCP risk measure and $D:\mathcal X^n\to\overline{\mathbb R}$ satisfies [+], [LI], [SI], [R]$_\phi$, [N]$_\phi$ and the semi-continuous form of [C]$_\phi$ (the standing assumptions of the “only if” part of the proof of Theorem 1). $R$ is the map (EC.1), $\mathcal A_\beta=\{R\le\beta\}$ and $\rho_\beta(X)=\inf\{m\in\mathbb R:X-m\in\mathcal A_\beta\}$.
--
--   1. For every $X\in\mathcal X$: $\phi(X)\le\rho_{1-\varepsilon}(X)$ for $0<\varepsilon<1$, and $\rho_{1+\varepsilon}(X)\le\phi(X)$ for $\varepsilon>0$.
--   2. If $\phi$ is moreover subadditive, then $\phi(X)\le\rho_\beta(X)$ for every $\beta>0$ and $X\in\mathcal X$.
--
--   Clause 1 pins the constructed class to $\phi$ at level $1$, which gives $\rho_\alpha=\phi$ in Theorem 1. Clause 2 is not printed: with clause 1 and right-continuity it gives $\rho_\beta=\phi$ for $\beta\ge1$ and shows the class is real valued, which the proof of Theorem 2 needs on p.37.
--
--   Differences from the source:
--   - reading: ρ_{1−ε} ≥ φ ≥ ρ_{1+ε} for all ε > 0 → φ ≤ ρ_{1−ε} for 0 < ε < 1, ρ_{1+ε} ≤ φ for ε > 0; reason: ρ_{1−ε} is a member of the class I = (0, ∞) only for ε < 1
--   - generalization: clause 1 only → clause 1 and clause 2 (φ subadditive ⇒ φ ≤ ρ_β for all β > 0); reason: clause 2 closes the step on p.37 that applies the convex-hull identity at levels β > α; dropping it gives the printed claim
--   - generalization: D satisfies the printed [C]φ: (D(X) − D(Yᵏ))₊ → 0 → D satisfies the semi-continuous form AxCLsc: d < D(X) implies eventually d < D(Yᵏ); reason: the printed axiom implies the semi-continuous one (proved in the mission's sanity file), so the statement specializes to the page's hypotheses
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, proof of Theorem 1, p.35

import Mathlib
import Definitions.Def_DivQuotient_ProofObjects

open MeasureTheory

namespace DivQuotient

/-- **Proof of Theorem 1, the sandwich** (Han–Lin–Wang, arXiv:2206.13679v6, p.35):
"Therefore, we get ρ_{1−ε} ⩾ φ ⩾ ρ_{1+ε} for all ε > 0."

Here `φ` is MCP, `D` satisfies [+], [LI], [SI], [R]φ, [N]φ and [C]φ (semi-continuous form),
and `ρ_β` is the constructed risk measure.

1. `φ ≤ ρ_{1−ε}` for `0 < ε < 1`, and `ρ_{1+ε} ≤ φ` for `ε > 0`;
2. (added) if `φ` is moreover subadditive, then `φ ≤ ρ_β` for every `β > 0`.

**Formalization Note.** `ρ_{1−ε}` is a member of the class `I = (0, ∞)` only for `ε < 1`.
Clause 2 is not printed; it closes the step on p.37 that applies the convex-hull identity at
levels `β > α`. -/
theorem sandwich {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (φ : Lp ℝ ⊤ P → ℝ) (hφ : IsMCP φ) (D : (Fin n → Lp ℝ ⊤ P) → EReal)
    (hNonneg : AxNonneg D) (hLI : AxLI D) (hSI : AxSI D) (hR : AxR φ D) (hN : AxN φ D)
    (hC : AxCLsc φ D) :
    (∀ ε : ℝ, 0 < ε → ∀ X : Lp ℝ ⊤ P,
        (ε < 1 → (φ X : EReal) ≤ rhoBeta φ D (1 - ε) X) ∧
          rhoBeta φ D (1 + ε) X ≤ (φ X : EReal)) ∧
      (IsSubadditive φ → ∀ β : ℝ, 0 < β → ∀ X : Lp ℝ ⊤ P, (φ X : EReal) ≤ rhoBeta φ D β X) := by sorry

end DivQuotient
