-- Prove2me | Theorems.Thm_DistQuantumQuery_proposition_4_7
-- name    : DistQuantumQuery.proposition_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:09.24547+00:00
-- url     : https://prove2.me/theorems/c525b797-3571-4559-8487-584c786b18be
-- title:
--   Proposition 4.7 — $Q(\Psi)\ge\bar\gamma^\mu_2(J-\Psi\mid\{\Delta_i\})/2$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $\mu$ a distribution on $\Sigma$, and $\Psi\in\mathrm{Pos}(\Sigma)$ a Gram matrix with $\Psi\circ I=I$. Then
--   $$
--   Q(\Psi)\ \ge\ \tfrac12\,\bar\gamma^\mu_2(J-\Psi\mid\{\Delta_i\}).
--   $$
--   This is the lower-bound half of the $\bar\gamma_2$ characterization of state generation.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: index register with basis |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential; reason: the same oracle model; Fin (d+1) always contains the start vector
--   - encoding: Q(Φ → Ψ): state families realized in a fixed, sufficiently large realization space V inside the work space → realizations existential in the algorithm's work space Option ι × Fin (d+1); reason: by Corollary 2.7 realizations with equal Gram matrices differ by an input-independent unitary, absorbed into U_0
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Proposition 4.7, p.40

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist
import Definitions.Def_DistQuantumQuery_gammaBar

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Proposition 4.7** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Proposition 4.7, p.40). Let `Σ ⊆ {0,1}^n`, `μ` a distribution on
`Σ` and `Ψ ∈ Pos(Σ)` a Gram matrix with `Ψ ∘ I = I`. Then `Q(Ψ) ≥ γ̄^μ₂(J − Ψ | {Δ_i}) / 2`.

**Formalization Note** `Q(Ψ) = Q(J → Ψ)` is `QConv S (allOnes S) Ψ`, cast to `ℝ≥0∞`. A Gram
matrix with unit diagonal is a positive semidefinite matrix with `Ψ ∘ I = I` (§2.3.3, p.16). -/
theorem proposition_4_7 {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (ι → Bool))
    (μ : S → ℝ) (hμ : IsDist μ) (Ψ : Matrix S S ℂ) (hΨ : Ψ.PosSemidef)
    (hΨd : Ψ ⊙ (1 : Matrix S S ℂ) = 1) :
    gammaBar μ (allOnes S - Ψ) (qfilters S) / 2 ≤ (QConv S (allOnes S) Ψ : ℝ≥0∞) := by sorry

end DistQuantumQuery
