-- Prove2me | Theorems.Thm_DistQuantumQuery_theorem_3_5
-- name    : DistQuantumQuery.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:18.512198+00:00
-- url     : https://prove2.me/theorems/2d64bc3f-aca3-4c03-a410-849332d0b73c
-- title:
--   Theorem 3.5 — fidelity characterization $Q^\mu_\varepsilon(f)=\min_{\Psi\in\mathcal G^\mu_\varepsilon(f)}Q(\Psi)$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, let $f\subseteq\Sigma\times\Omega$ be a search problem (every $f(x)$ nonempty), $\mu$ a distribution on $\Sigma$ and $\varepsilon\in[0,1)$. Then
--   $$
--   Q^\mu_\varepsilon(f)=\min_{\Psi\in\mathcal G^\mu_\varepsilon(f)}Q(\Psi),
--   $$
--   where $Q(\Psi)=Q(J\to\Psi)$ is the state-generation complexity of the Gram matrix $\Psi$, and the minimum is attained.
--
--   This reduces distributional query complexity to the query complexity of Gram matrices close (in fidelity, under $\mu$) to a valid witness, and is the starting point of every bound in the paper.
--
--   **Formalization Note** The minimum is `IsLeast` of the set of values $Q(\Psi)$, $\Psi$ a target.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: index register with basis |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential; reason: the same oracle model; Fin (d+1) always contains the start vector
--   - reading: projective measurement: Π_s² = Π_s, Π_sΠ_t = 0, Σ_r Π_r = I (§2.3.2) → each Π_s also Hermitian; reason: the same paragraph reads outcome probabilities as Tr[Π_s ρ], which requires orthogonal projectors
--   - encoding: Q(Φ → Ψ): state families realized in a fixed, sufficiently large realization space V inside the work space → realizations existential in the algorithm's work space Option ι × Fin (d+1); reason: by Corollary 2.7 realizations with equal Gram matrices differ by an input-independent unitary, absorbed into U_0
--   - encoding: G^μ_ε(f): max_{W ∈ W^μ_f} F(W ∘ |μ⟩⟨μ|, Ψ ∘ |μ⟩⟨μ|) ≥ √(1−ε) → ∃ W ∈ W^μ_f with F ≥ √(1−ε); reason: the source writes max, i.e. the maximum is attained
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Theorem 3.5, p.24

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist
import Definitions.Def_DistQuantumQuery_Adv

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Theorem 3.5 (Fidelity characterization)** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Theorem 3.5, p.24).
For `Σ ⊆ {0,1}^n`, a search problem `f ⊆ Σ × Ω`, a distribution `μ` on `Σ` and `ε ∈ [0,1)`,
`Q^μ_ε(f) = min_{Ψ ∈ G^μ_ε(f)} Q(Ψ)`.

**Formalization Note** The search problem is a total relation `R` (`∀ x, ∃ s, R x s`, the
standing convention of §2.4, p.17). "min" is `IsLeast` (the minimum is attained). `Q(Ψ)` is
`QConv S (allOnes S) Ψ`. -/
theorem theorem_3_5 {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (S : Finset (ι → Bool)) (R : S → Ω → Prop) (hR : ∀ x, ∃ s, R x s)
    (μ : S → ℝ) (hμ : IsDist μ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    IsLeast {q : ℕ∞ | ∃ Ψ ∈ Targets μ R ε, q = QConv S (allOnes S) Ψ} (Qdist S μ R ε) := by sorry

end DistQuantumQuery
