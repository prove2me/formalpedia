-- Prove2me | Theorems.Thm_DivQuotient_ec1_a
-- name    : DivQuotient.ec1_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:43.342428+00:00
-- url     : https://prove2.me/theorems/76217830-6830-4c27-94cc-ef09bb4e9669
-- title:
--   Proof of Theorem 1, (EC.1) and claim (a) — $D$ depends only on $S(\mathbf X_\phi)$, and $R(S(\mathbf X_\phi))=D(\mathbf X)$
-- statement:
--   Throughout, $\phi$ is an MCP risk measure and $D:\mathcal X^n\to\overline{\mathbb R}$ satisfies [+], [LI], [SI], [R]$_\phi$, [N]$_\phi$ and the semi-continuous form of [C]$_\phi$ (the standing assumptions of the “only if” part of the proof of Theorem 1). $R$ is the map (EC.1), $\mathcal A_\beta=\{R\le\beta\}$ and $\rho_\beta(X)=\inf\{m\in\mathbb R:X-m\in\mathcal A_\beta\}$.
--
--   1. If $S(\mathbf X_\phi)=S(\mathbf Y_\phi)$, then $D(\mathbf X)=D(\mathbf Y)$.
--   2. (a) For every $\mathbf X\in\mathcal X^n$,
--   $$
--   R\big(S(\mathbf X_\phi)\big)=D(\mathbf X).
--   $$
--
--   So $D$ is a function of the centred aggregate loss $S(\mathbf X_\phi)$, and $R$ is that function.
--
--   Differences from the source:
--   - generalization: D satisfies the printed [C]φ: (D(X) − D(Yᵏ))₊ → 0 → D satisfies the semi-continuous form AxCLsc: d < D(X) implies eventually d < D(Yᵏ); reason: the printed axiom implies the semi-continuous one (proved in the mission's sanity file), so the statement specializes to the page's hypotheses
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, proof of Theorem 1, p.34 (the paragraph before (EC.1), and claim (a))

import Mathlib
import Definitions.Def_DivQuotient_ProofObjects

open MeasureTheory

namespace DivQuotient

/-- **Proof of Theorem 1, the step before (EC.1) and claim (a)** (Han–Lin–Wang,
arXiv:2206.13679v6, p.34). Let `φ` be MCP and let `D` satisfy [+], [LI], [SI], [R]φ, [N]φ
and [C]φ (semi-continuous form). Then

1. `D(X) = D(Y)` whenever `S(X_φ) = S(Y_φ)`;
2. (a) `R(S(X_φ)) = D(X)` for every `X ∈ 𝒳ⁿ`, with `R` the map (EC.1).

**Formalization Note.** [C]φ is taken in the semi-continuous form `AxCLsc`, which the printed
form implies. -/
theorem ec1_a {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (φ : Lp ℝ ⊤ P → ℝ) (hφ : IsMCP φ) (D : (Fin n → Lp ℝ ⊤ P) → EReal)
    (hNonneg : AxNonneg D) (hLI : AxLI D) (hSI : AxSI D) (hR : AxR φ D) (hN : AxN φ D)
    (hC : AxCLsc φ D) :
    (∀ X Y : Fin n → Lp ℝ ⊤ P, S (phiCenter φ X) = S (phiCenter φ Y) → D X = D Y) ∧
      ∀ X : Fin n → Lp ℝ ⊤ P, Rmap φ D (S (phiCenter φ X)) = D X := by sorry

end DivQuotient
