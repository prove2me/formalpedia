-- Prove2me | Theorems.Thm_DistQuantumQuery_proposition_5_5
-- name    : DistQuantumQuery.proposition_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:57.379758+00:00
-- url     : https://prove2.me/theorems/0ca92992-f461-441f-a7b3-8c56dbb5b019
-- title:
--   Proposition 5.5 — $Q^\mu_{(\sqrt\varepsilon+\sqrt\eta)^2}(f)\le\frac4\eta\mathrm{Adv}^\mu_\varepsilon(f)$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f\subseteq\Sigma\times\Omega$ a search problem, $\mu$ a distribution, and $\varepsilon\in[0,1)$, $\eta\in(0,1)$ with $\sqrt\varepsilon+\sqrt\eta<1$. Then
--   $$
--   Q^\mu_{(\sqrt\varepsilon+\sqrt\eta)^2}(f)\le\frac4\eta\,\mathrm{Adv}^\mu_\varepsilon(f).
--   $$
--   Together with Proposition 5.4 this shows that $\mathrm{Adv}^\mu$ characterizes $Q^\mu$ up to a change in the error.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: index register with basis |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential; reason: the same oracle model; Fin (d+1) always contains the start vector
--   - reading: projective measurement: Π_s² = Π_s, Π_sΠ_t = 0, Σ_r Π_r = I (§2.3.2) → each Π_s also Hermitian; reason: the same paragraph reads outcome probabilities as Tr[Π_s ρ], which requires orthogonal projectors
--   - encoding: G^μ_ε(f): max_{W ∈ W^μ_f} F(W ∘ |μ⟩⟨μ|, Ψ ∘ |μ⟩⟨μ|) ≥ √(1−ε) → ∃ W ∈ W^μ_f with F ≥ √(1−ε); reason: the source writes max, i.e. the maximum is attained
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Proposition 5.5, p.44

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist
import Definitions.Def_DistQuantumQuery_Adv

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Proposition 5.5** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Proposition 5.5, p.44). Let `Σ ⊆ {0,1}^n`, `f ⊆ Σ × Ω` a search
problem, `μ` a distribution, and `ε ∈ [0,1)`, `η ∈ (0,1)` with `√ε + √η < 1`. Then
`Q^μ_{(√ε+√η)²}(f) ≤ (4/η) · Adv^μ_ε(f)`.

**Formalization Note** The search problem is a total relation `R`; the bound is in `ℝ≥0∞`. -/
theorem proposition_5_5 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (S : Finset (ι → Bool)) (R : S → Ω → Prop) (hR : ∀ x, ∃ s, R x s)
    (μ : S → ℝ) (hμ : IsDist μ) (ε η : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hη0 : 0 < η)
    (hη1 : η < 1) (hεη : Real.sqrt ε + Real.sqrt η < 1) :
    (Qdist S μ R ((Real.sqrt ε + Real.sqrt η) ^ 2) : ℝ≥0∞) ≤
      ENNReal.ofReal (4 / η) * Adv S μ R ε := by sorry

end DistQuantumQuery
