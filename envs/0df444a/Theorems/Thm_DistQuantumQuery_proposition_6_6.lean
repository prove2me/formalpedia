-- Prove2me | Theorems.Thm_DistQuantumQuery_proposition_6_6
-- name    : DistQuantumQuery.proposition_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:55.063243+00:00
-- url     : https://prove2.me/theorems/32ce0e58-fe38-4662-84fc-2b71346703b6
-- title:
--   Proposition 6.6 — $\mathrm{Adv}^\mu_{(2+\eta)\delta}(f)\le2Q^\mu_{(2+\eta)\delta}(f)=O(\mathrm{rAdv}^\mu_\delta(f)/(\eta^2\delta))$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f:\Sigma\to\Omega$ functional, $\delta\in(0,1)$, $\mu$ a distribution and $\eta\in(0,1]$ with $(2+\eta)\delta<1$. Then
--   $$
--   \mathrm{Adv}^\mu_{(2+\eta)\delta}(f)\le2\,Q^\mu_{(2+\eta)\delta}(f)=O\!\left(\frac{\mathrm{rAdv}^\mu_\delta(f)}{\eta^2\delta}\right).
--   $$
--   The relaxed adversary measure therefore upper-bounds distributional query complexity, with a loss in the error.
--
--   **Formalization Note** The $O(\cdot)$ is an absolute constant $C>0$, chosen before every instance: $2Q^\mu_{(2+\eta)\delta}(f)\le C\,\mathrm{rAdv}^\mu_\delta(f)/(\eta^2\delta)$.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: index register with basis |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential; reason: the same oracle model; Fin (d+1) always contains the start vector
--   - reading: projective measurement: Π_s² = Π_s, Π_sΠ_t = 0, Σ_r Π_r = I (§2.3.2) → each Π_s also Hermitian; reason: the same paragraph reads outcome probabilities as Tr[Π_s ρ], which requires orthogonal projectors
--   - encoding: G^μ_ε(f): max_{W ∈ W^μ_f} F(W ∘ |μ⟩⟨μ|, Ψ ∘ |μ⟩⟨μ|) ≥ √(1−ε) → ∃ W ∈ W^μ_f with F ≥ √(1−ε); reason: the source writes max, i.e. the maximum is attained
--   - encoding: constants uniform over all instances → instances quantified with index and output types in Type (universe 0); reason: every instance of the source has finite index and output sets, which live in Type up to relabelling
--   - reading: O(rAdv^μ_δ(f)/(η²δ)) → ∃ C > 0, chosen before Σ, f, μ, δ, η: 2Q ≤ C·rAdv^μ_δ(f)/(η²δ); reason: the O(·) carries no subscript, and the error parameters may depend on n (p.22), so the constant is absolute
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Proposition 6.6, p.50

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist
import Definitions.Def_DistQuantumQuery_Adv
import Definitions.Def_DistQuantumQuery_rAdv

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Proposition 6.6** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Proposition 6.6, p.50). Let `Σ ⊆ {0,1}^n`, `f : Σ → Ω` functional,
`δ ∈ (0,1)`, `μ` a distribution and `η ∈ (0,1]` with `(2 + η)δ < 1`. Then
`Adv^μ_{(2+η)δ}(f) ≤ 2 Q^μ_{(2+η)δ}(f) = O(rAdv^μ_δ(f) / (η²δ))`.

**Formalization Note** The `O(·)` constant `C` is absolute: it is chosen before the positions,
the output set, `Σ`, `f`, `μ`, `δ` and `η` (the proof, p.52, gives `T ≤ 64 rAdv^μ_δ(f)/(η²δ)`).
Index and output types range over `Type`. Values in `ℝ≥0∞`. -/
theorem proposition_6_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι Ω : Type) [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
      (S : Finset (ι → Bool)) (f : S → Ω) (μ : S → ℝ) (δ η : ℝ), IsDist μ → 0 < δ → δ < 1 →
      0 < η → η ≤ 1 → (2 + η) * δ < 1 →
      Adv S μ (graphRel f) ((2 + η) * δ) ≤ 2 * (Qdist S μ (graphRel f) ((2 + η) * δ) : ℝ≥0∞) ∧
      2 * (Qdist S μ (graphRel f) ((2 + η) * δ) : ℝ≥0∞) ≤
        ENNReal.ofReal C * rAdv S μ f δ / ENNReal.ofReal (η ^ 2 * δ) := by sorry

end DistQuantumQuery
