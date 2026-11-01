-- Prove2me | Theorems.Thm_DivQuotient_coherent_of_portfolioConvex
-- name    : DivQuotient.coherent_of_portfolioConvex
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:24.092824+00:00
-- url     : https://prove2.me/theorems/95c4f638-5ca0-4707-8236-a4fce9ed0515
-- title:
--   Proof of Theorem 2 — under [PC] each constructed $\rho_\beta$ is real valued and coherent
-- statement:
--   Let $n\ge4$, let $\phi$ be a non-linear coherent risk measure, and let $D$ satisfy [+], [LI], [SI], [R]$_\phi$, [N]$_\phi$, the semi-continuous form of [C]$_\phi$, and [PC]. Let $\rho_\beta(X)=\inf\{m\in\mathbb R:X-m\in\mathcal A_\beta\}$ be the class constructed in the proof of Theorem 1. Then for every $\beta>0$:
--
--   1. $-\infty<\rho_\beta(X)<\infty$ for all $X$, so $\rho_\beta$ is real valued;
--   2. $\rho_\beta$ is a coherent risk measure.
--
--   This is the last step of the “only if” direction of Theorem 2: portfolio convexity of the index forces convexity, hence coherence, of every risk measure in the representing class.
--
--   **Formalization Note** $\rho_\beta$ is defined in $\overline{\mathbb R}$; clause 2 is stated for its real part `toReal`, which by clause 1 is $\rho_\beta$ itself.
--
--   Differences from the source:
--   - generalization: ρ_β is coherent → ρ_β is real valued and coherent; reason: real-valuedness is not printed but needed for ρ_β to be a risk measure 𝒳 → ℝ (p.4); it follows from φ ≤ ρ_β for subadditive φ; dropping it gives the printed claim
--   - generalization: D satisfies the printed [C]φ: (D(X) − D(Yᵏ))₊ → 0 → D satisfies the semi-continuous form AxCLsc: d < D(X) implies eventually d < D(Yᵏ); reason: the printed axiom implies the semi-continuous one (proved in the mission's sanity file), so the statement specializes to the page's hypotheses
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
--   - encoding: ρ_β : 𝒳 → ℝ → (rhoBeta φ D β X).toReal, with rhoBeta in EReal; reason: clause 1 says every value is finite, so toReal changes no value
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, proof of Theorem 2, p.37

import Mathlib
import Definitions.Def_DivQuotient_ProofObjects

open MeasureTheory

namespace DivQuotient

/-- **Proof of Theorem 2, coherence of `ρ_β`** (Han–Lin–Wang, arXiv:2206.13679v6, p.37):
"Hence, ρ_β is quasi-convex. Since ρ_β is MCP, we further have ρ_β is coherent."

Let `n ≥ 4`, let `φ` be a non-linear coherent risk measure, and let `D` satisfy [+], [LI], [SI],
[R]φ, [N]φ, [C]φ (semi-continuous form) and [PC]. Then every member `ρ_β`, `β > 0`, of the class
constructed in the proof of Theorem 1, `ρ_β(X) = inf{m ∈ ℝ : X − m ∈ 𝒜_β}`, is real valued and
is a coherent risk measure.

**Formalization Note.** `ρ_β` is defined in `ℝ̄`; the first clause says it never takes the value
`−∞` or `+∞`, so `fun X => (ρ_β X).toReal` is `ρ_β` itself. Real-valuedness is not printed; for
subadditive `φ` it follows from `φ ≤ ρ_β` (the sandwich milestone, clause 2). -/
theorem coherent_of_portfolioConvex {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 4 ≤ n) (φ : Lp ℝ ⊤ P → ℝ) (hφ : IsCoherent φ)
    (hnl : ¬ IsLinear φ) (D : (Fin n → Lp ℝ ⊤ P) → EReal)
    (hNonneg : AxNonneg D) (hLI : AxLI D) (hSI : AxSI D) (hR : AxR φ D) (hN : AxN φ D)
    (hC : AxCLsc φ D) (hPC : AxPC D) :
    ∀ β : ℝ, 0 < β →
      (∀ X : Lp ℝ ⊤ P, rhoBeta φ D β X ≠ ⊥ ∧ rhoBeta φ D β X ≠ ⊤) ∧
        IsCoherent (fun X => (rhoBeta φ D β X).toReal) := by sorry

end DivQuotient
