-- Prove2me | Theorems.Thm_DistQuantumQuery_proposition_6_5
-- name    : DistQuantumQuery.proposition_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:15.319405+00:00
-- url     : https://prove2.me/theorems/cb454b3a-e621-4851-bdbe-f8e2f201720d
-- title:
--   Proposition 6.5 — $\mathrm{Adv}^\mu_\varepsilon(f)\ge\mathrm{rAdv}^\mu_{4\sqrt\varepsilon}(f)/2$, and $\ge\mathrm{rAdv}^\mu_{2\sqrt{\varepsilon(1-\varepsilon)}}(f)$ for decision problems
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f:\Sigma\to\Omega$ functional, $\mu$ a distribution and $\varepsilon\in[0,1/2)$. Then for $\varepsilon\le1/16$,
--   $$
--   \mathrm{Adv}^\mu_\varepsilon(f)\ge\tfrac12\,\mathrm{rAdv}^\mu_{4\sqrt\varepsilon}(f).
--   $$
--   Moreover, if $f:\Sigma\to\{0,1\}$ is a decision problem, then for every $\varepsilon\in[0,1/2)$,
--   $$
--   \mathrm{Adv}^\mu_\varepsilon(f)\ge\mathrm{rAdv}^\mu_{2\sqrt{\varepsilon(1-\varepsilon)}}(f).
--   $$
--   These give the lower bounds of Corollary 6.9.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: G^μ_ε(f): max_{W ∈ W^μ_f} F(W ∘ |μ⟩⟨μ|, Ψ ∘ |μ⟩⟨μ|) ≥ √(1−ε) → ∃ W ∈ W^μ_f with F ≥ √(1−ε); reason: the source writes max, i.e. the maximum is attained
--   - encoding: “if f is a decision problem” (Ω = {0,1}) → a second clause for every g : Σ → Bool on the same Σ and μ; reason: Bool is {0,1}; the decision clause is stated for all decision problems on the same data
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Proposition 6.5, p.49

import Mathlib
import Definitions.Def_DistQuantumQuery_Adv
import Definitions.Def_DistQuantumQuery_rAdv

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Proposition 6.5** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Proposition 6.5, p.49). Let `Σ ⊆ {0,1}^n`, `f : Σ → Ω` functional,
`μ` a distribution and `ε ∈ [0, 1/2)`. Then for `ε ≤ 1/16`, `Adv^μ_ε(f) ≥ rAdv^μ_{4√ε}(f)/2`.
Moreover, if `f : Σ → {0,1}` is a decision problem, then for every `ε ∈ [0, 1/2)`,
`Adv^μ_ε(f) ≥ rAdv^μ_{2√(ε(1−ε))}(f)`.

**Formalization Note** The decision clause is stated for every `g : Σ → Bool` on the same `Σ`
and `μ`. Values in `ℝ≥0∞`. -/
theorem proposition_6_5 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (S : Finset (ι → Bool)) (f : S → Ω) (μ : S → ℝ) (hμ : IsDist μ) :
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 → ε ≤ 1 / 16 →
      rAdv S μ f (4 * Real.sqrt ε) / 2 ≤ Adv S μ (graphRel f) ε) ∧
    (∀ g : S → Bool, ∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 →
      rAdv S μ g (2 * Real.sqrt (ε * (1 - ε))) ≤ Adv S μ (graphRel g) ε) := by sorry

end DistQuantumQuery
