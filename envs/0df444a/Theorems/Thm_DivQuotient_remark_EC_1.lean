-- Prove2me | Theorems.Thm_DivQuotient_remark_EC_1
-- name    : DivQuotient.remark_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:54.046025+00:00
-- url     : https://prove2.me/theorems/5fa16516-eb9b-4b66-ac99-c495b33ac42a
-- title:
--   Remark EC.1 — the constructed class $\beta\mapsto\rho_\beta$ is right-continuous
-- statement:
--   Throughout, $\phi$ is an MCP risk measure and $D:\mathcal X^n\to\overline{\mathbb R}$ satisfies [+], [LI], [SI], [R]$_\phi$, [N]$_\phi$ and the semi-continuous form of [C]$_\phi$ (the standing assumptions of the “only if” part of the proof of Theorem 1). $R$ is the map (EC.1), $\mathcal A_\beta=\{R\le\beta\}$ and $\rho_\beta(X)=\inf\{m\in\mathbb R:X-m\in\mathcal A_\beta\}$.
--
--   For every $X\in\mathcal X$ and $\beta>0$,
--
--   $$
--   \lim_{\gamma\downarrow\beta}\rho_\gamma(X)=\rho_\beta(X)\quad\text{in }\overline{\mathbb R}.
--   $$
--
--   The paper derives this from $\bigcap_{\gamma>\beta}\mathcal A_\gamma=\mathcal A_\beta$; it is used in the proof of Theorem 2.
--
--   Differences from the source:
--   - generalization: D satisfies the printed [C]φ: (D(X) − D(Yᵏ))₊ → 0 → D satisfies the semi-continuous form AxCLsc: d < D(X) implies eventually d < D(Yᵏ); reason: the printed axiom implies the semi-continuous one (proved in the mission's sanity file), so the statement specializes to the page's hypotheses
--   - generalization: (Ω, ℱ, ℙ) an atomless probability space (Notation, p.4) → any probability space; reason: no step of the proof uses atomlessness; an atomless space is a special case
--   - encoding: 𝒳 = L∞ with almost surely equal random variables identified; vectors (X₁, …, Xₙ); D : 𝒳ⁿ → ℝ̄ → Lp ℝ ⊤ P with its a.e. order and L∞ norm; Fin n → Lp ℝ ⊤ P (0-based); EReal; reason: Lean convention; same objects
-- source:
--   Han, Lin & Wang, Diversification quotients: Quantifying diversification via risk measures, arXiv:2206.13679v6, Remark EC.1, p.35

import Mathlib
import Definitions.Def_DivQuotient_ProofObjects

open MeasureTheory Filter Topology

namespace DivQuotient

/-- **Remark EC.1** (Han–Lin–Wang, arXiv:2206.13679v6, p.35): "In the proof of Theorem 1, the
constructed class of risk measures (ρ_β)_{β∈I} exhibits right continuity in β."

Here `φ` is MCP, `D` satisfies [+], [LI], [SI], [R]φ, [N]φ and [C]φ (semi-continuous form),
and `ρ_β` is the constructed risk measure. For every `X` and `β > 0`,
`ρ_γ(X) → ρ_β(X)` as `γ ↓ β`, in `ℝ̄`. -/
theorem remark_EC_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (φ : Lp ℝ ⊤ P → ℝ) (hφ : IsMCP φ) (D : (Fin n → Lp ℝ ⊤ P) → EReal)
    (hNonneg : AxNonneg D) (hLI : AxLI D) (hSI : AxSI D) (hR : AxR φ D) (hN : AxN φ D)
    (hC : AxCLsc φ D) (X : Lp ℝ ⊤ P) (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun γ : ℝ => rhoBeta φ D γ X) (𝓝[>] β) (𝓝 (rhoBeta φ D β X)) := by sorry

end DivQuotient
