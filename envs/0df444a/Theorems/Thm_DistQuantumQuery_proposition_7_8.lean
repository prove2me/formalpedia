-- Prove2me | Theorems.Thm_DistQuantumQuery_proposition_7_8
-- name    : DistQuantumQuery.proposition_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:06.83549+00:00
-- url     : https://prove2.me/theorems/9d24a6e0-9f7a-4ceb-bc9c-112f93ab3004
-- title:
--   Proposition 7.8 — $\mathrm{Adv}^\eta_\varepsilon(f\circ g)\ge\mathrm{Adv}^\mu_\varepsilon(f)\,\mathrm{sfAdv}(g)$ and the same for $\mathrm{rAdv}_\delta$
-- statement:
--   Let $f:\Sigma\to\Omega$ be functional on $\Sigma\subseteq\{0,1\}^n$, $\mu$ a distribution on $\Sigma$, $g:\Sigma_g\to\{0,1\}$ a decision problem on $\Sigma_g\subseteq\{0,1\}^m$, $\nu_0,\nu_1$ distributions supported on $g^{-1}(0)$ and $g^{-1}(1)$ (i.e. $\nu_b(x)\ne0\Rightarrow g(x)=b$), and $\eta=\mu\circ(\nu_0,\nu_1)$. Then for $\varepsilon\in(0,1/2)$ and $\delta\in(0,1)$,
--   $$
--   \mathrm{Adv}^\eta_\varepsilon(f\circ g)\ge\mathrm{Adv}^\mu_\varepsilon(f)\cdot\mathrm{sfAdv}^{(\nu_0,\nu_1)}(g),\qquad
--   \mathrm{rAdv}^\eta_\delta(f\circ g)\ge\mathrm{rAdv}^\mu_\delta(f)\cdot\mathrm{sfAdv}^{(\nu_0,\nu_1)}(g).
--   $$
--   These are the adversary composition theorems (the first two items of Theorem 7.1) that the main theorem converts into query complexity.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: G^μ_ε(f): max_{W ∈ W^μ_f} F(W ∘ |μ⟩⟨μ|, Ψ ∘ |μ⟩⟨μ|) ≥ √(1−ε) → ∃ W ∈ W^μ_f with F ≥ √(1−ε); reason: the source writes max, i.e. the maximum is attained
--   - encoding: composed inputs in {0,1}^{mn} → bit strings on ι × κ (block i, bit j); reason: relabelling positions
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Proposition 7.8, p.62; Theorem 7.1, p.55

import Mathlib
import Definitions.Def_DistQuantumQuery_Adv
import Definitions.Def_DistQuantumQuery_sfAdv
import Definitions.Def_DistQuantumQuery_compose

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Proposition 7.8** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Proposition 7.8, p.62). Let `f : Σ → Ω`, `g`, `μ`, `ν₀`, `ν₁` be as in
Theorem 7.1 and `η = μ ∘ (ν₀, ν₁)`. Then for `ε ∈ (0, 1/2)` and `δ ∈ (0,1)`,
`Adv^η_ε(f ∘ g) ≥ Adv^μ_ε(f) · sfAdv^{(ν₀,ν₁)}(g)` and
`rAdv^η_δ(f ∘ g) ≥ rAdv^μ_δ(f) · sfAdv^{(ν₀,ν₁)}(g)`.

**Formalization Note** "As in Theorem 7.1" (p.55): `Σ ⊆ {0,1}^n`, `f` functional, `μ` a
distribution on `Σ`; `Σ_g ⊆ {0,1}^m`, `g` decision, `ν_b` distributions supported on `g⁻¹(b)`.
The composed problem lives on `g⁻¹(Σ) ⊆ {0,1}^{ι × κ}`. Values in `ℝ≥0∞`. -/
theorem proposition_7_8 {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω] (S : Finset (ι → Bool)) (f : S → Ω) (μ : S → ℝ)
    (hμ : IsDist μ) (Sg : Finset (κ → Bool)) (g : Sg → Bool) (ν₀ ν₁ : Sg → ℝ) (hν₀ : IsDist ν₀) (hν₁ : IsDist ν₁)
    (hs₀ : ∀ x, ν₀ x ≠ 0 → g x = false) (hs₁ : ∀ x, ν₁ x ≠ 0 → g x = true)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Adv S μ (graphRel f) ε * sfAdv Sg g ν₀ ν₁ ≤
        Adv (compDomain S Sg g) (compDist g μ ν₀ ν₁) (graphRel (compose f g)) ε ∧
      rAdv S μ f δ * sfAdv Sg g ν₀ ν₁ ≤
        rAdv (compDomain S Sg g) (compDist g μ ν₀ ν₁) (compose f g) δ := by sorry

end DistQuantumQuery
