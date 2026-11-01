-- Prove2me | Theorems.Thm_DivQuotient_ec1_e
-- name    : DivQuotient.ec1_e
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:46.901719+00:00
-- url     : https://prove2.me/theorems/5ff9923c-0fd3-4bdf-961e-997b08469059
-- title:
--   Proof of Theorem 1, claim (e) — $\lim_{c\downarrow0}R(S(\mathbf X_\phi)-c)=R(S(\mathbf X_\phi))$
-- statement:
--   Throughout, $\phi$ is an MCP risk measure and $D:\mathcal X^n\to\overline{\mathbb R}$ satisfies [+], [LI], [SI], [R]$_\phi$, [N]$_\phi$ and the semi-continuous form of [C]$_\phi$ (the standing assumptions of the “only if” part of the proof of Theorem 1). $R$ is the map (EC.1), $\mathcal A_\beta=\{R\le\beta\}$ and $\rho_\beta(X)=\inf\{m\in\mathbb R:X-m\in\mathcal A_\beta\}$.
--
--   For every $\mathbf X\in\mathcal X^n$,
--
--   $$
--   \lim_{c\downarrow0}R\big(S(\mathbf X_\phi)-c\big)=R\big(S(\mathbf X_\phi)\big),
--   $$
--
--   the limit being taken in $\overline{\mathbb R}$ as $c\to0$ from above; this includes the case $R(S(\mathbf X_\phi))=\infty$.
--
--   This left-continuity of $R$ along constant shifts is what lets the risk measures $\rho_\beta$ recover $D$ exactly.
--
--   Differences from the source:
--   - generalization: D satisfies the printed [C]φ: (D(X) − D(Yᵏ))₊ → 0 → D satisfies the semi-continuous form AxCLsc: d < D(X) implies eventually d < D(Yᵏ); reason: the printed axiom implies the semi-continuous one (proved in the mission's sanity file), so the statement specializes to the page's hypotheses
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, proof of Theorem 1, claim (e), p.34

import Mathlib
import Definitions.Def_DivQuotient_ProofObjects

open MeasureTheory Filter Topology

namespace DivQuotient

/-- **Proof of Theorem 1, claim (e)** (Han–Lin–Wang, arXiv:2206.13679v6, p.34):
"(e) lim_{c↓0} R(S(X_φ) − c) = R(S(X_φ)) for X ∈ 𝒳ⁿ."

Here `φ` is MCP, `D` satisfies [+], [LI], [SI], [R]φ, [N]φ and [C]φ (semi-continuous form),
and `R` is the map (EC.1). The limit is from the right in `c`, in `ℝ̄`, and includes the
case `R(S(X_φ)) = ∞`. -/
theorem ec1_e {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (φ : Lp ℝ ⊤ P → ℝ) (hφ : IsMCP φ) (D : (Fin n → Lp ℝ ⊤ P) → EReal)
    (hNonneg : AxNonneg D) (hLI : AxLI D) (hSI : AxSI D) (hR : AxR φ D) (hN : AxN φ D)
    (hC : AxCLsc φ D) (X : Fin n → Lp ℝ ⊤ P) :
    Tendsto (fun c : ℝ => Rmap φ D (S (phiCenter φ X) - Lp.const ⊤ P c)) (𝓝[>] 0)
      (𝓝 (Rmap φ D (S (phiCenter φ X)))) := by sorry

end DivQuotient
