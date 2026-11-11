-- Prove2me | Theorems.Thm_DistQuantumQuery_proposition_5_4
-- name    : DistQuantumQuery.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:16.194964+00:00
-- url     : https://prove2.me/theorems/c55136e1-5fc0-4d9f-8f3c-7812bca436d3
-- title:
--   Proposition 5.4 — $Q^\mu_\varepsilon(f)\ge\mathrm{Adv}^\mu_\varepsilon(f)/2$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f\subseteq\Sigma\times\Omega$ a search problem, $\mu$ a distribution and $\varepsilon\in[0,1)$. Then
--   $$
--   Q^\mu_\varepsilon(f)\ \ge\ \tfrac12\,\mathrm{Adv}^\mu_\varepsilon(f).
--   $$
--   The distributional adversary measure lower-bounds distributional query complexity with no loss in the error.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: index register with basis |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential; reason: the same oracle model; Fin (d+1) always contains the start vector
--   - reading: projective measurement: Π_s² = Π_s, Π_sΠ_t = 0, Σ_r Π_r = I (§2.3.2) → each Π_s also Hermitian; reason: the same paragraph reads outcome probabilities as Tr[Π_s ρ], which requires orthogonal projectors
--   - encoding: G^μ_ε(f): max_{W ∈ W^μ_f} F(W ∘ |μ⟩⟨μ|, Ψ ∘ |μ⟩⟨μ|) ≥ √(1−ε) → ∃ W ∈ W^μ_f with F ≥ √(1−ε); reason: the source writes max, i.e. the maximum is attained
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Proposition 5.4, p.44

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist
import Definitions.Def_DistQuantumQuery_Adv

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Proposition 5.4** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Proposition 5.4, p.44). Let `Σ ⊆ {0,1}^n`, `f ⊆ Σ × Ω` a search
problem, `μ` a distribution on `Σ` and `ε ∈ [0,1)`. Then `Q^μ_ε(f) ≥ Adv^μ_ε(f) / 2`.

**Formalization Note** The search problem is a total relation `R`; values in `ℝ≥0∞`. -/
theorem proposition_5_4 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (S : Finset (ι → Bool)) (R : S → Ω → Prop) (hR : ∀ x, ∃ s, R x s)
    (μ : S → ℝ) (hμ : IsDist μ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Adv S μ R ε / 2 ≤ (Qdist S μ R ε : ℝ≥0∞) := by sorry

end DistQuantumQuery
