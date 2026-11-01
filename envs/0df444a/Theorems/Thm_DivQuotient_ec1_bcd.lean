-- Prove2me | Theorems.Thm_DivQuotient_ec1_bcd
-- name    : DivQuotient.ec1_bcd
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:57.365533+00:00
-- url     : https://prove2.me/theorems/806ffd09-02c5-40ab-962a-dd639a895d3c
-- title:
--   Proof of Theorem 1, claims (b), (c), (d) — $R$ is scale invariant, monotone, and $R(0)=0$
-- statement:
--   Throughout, $\phi$ is an MCP risk measure and $D:\mathcal X^n\to\overline{\mathbb R}$ satisfies [+], [LI], [SI], [R]$_\phi$, [N]$_\phi$ and the semi-continuous form of [C]$_\phi$ (the standing assumptions of the “only if” part of the proof of Theorem 1). $R$ is the map (EC.1), $\mathcal A_\beta=\{R\le\beta\}$ and $\rho_\beta(X)=\inf\{m\in\mathbb R:X-m\in\mathcal A_\beta\}$.
--
--   1. (b) $R(\lambda X)=R(X)$ for all $\lambda>0$ and $X\in\mathcal X$;
--   2. (c) $R(X)\le R(Y)$ whenever $X\le Y$;
--   3. (d) $R(0)=0$.
--
--   These make each $\mathcal A_\beta$ a conic, decreasing set containing $0$.
--
--   Differences from the source:
--   - generalization: D satisfies the printed [C]φ: (D(X) − D(Yᵏ))₊ → 0 → D satisfies the semi-continuous form AxCLsc: d < D(X) implies eventually d < D(Yᵏ); reason: the printed axiom implies the semi-continuous one (proved in the mission's sanity file), so the statement specializes to the page's hypotheses
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, proof of Theorem 1, claims (b), (c), (d), p.34

import Mathlib
import Definitions.Def_DivQuotient_ProofObjects

open MeasureTheory

namespace DivQuotient

/-- **Proof of Theorem 1, claims (b), (c), (d)** (Han–Lin–Wang, arXiv:2206.13679v6, p.34):
"(b) R(λX) = R(X) for all λ > 0 and X ∈ 𝒳. (c) R(X) ⩽ R(Y) for all X, Y ∈ 𝒳 with X ⩽ Y.
(d) R(0) = 0."

Here `φ` is MCP, `D` satisfies [+], [LI], [SI], [R]φ, [N]φ and [C]φ (semi-continuous form),
and `R` is the map (EC.1). -/
theorem ec1_bcd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (φ : Lp ℝ ⊤ P → ℝ) (hφ : IsMCP φ) (D : (Fin n → Lp ℝ ⊤ P) → EReal)
    (hNonneg : AxNonneg D) (hLI : AxLI D) (hSI : AxSI D) (hR : AxR φ D) (hN : AxN φ D)
    (hC : AxCLsc φ D) :
    (∀ (l : ℝ) (X : Lp ℝ ⊤ P), 0 < l → Rmap φ D (l • X) = Rmap φ D X) ∧
      (∀ X Y : Lp ℝ ⊤ P, X ≤ Y → Rmap φ D X ≤ Rmap φ D Y) ∧
      Rmap φ D 0 = 0 := by sorry

end DivQuotient
