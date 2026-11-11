-- Prove2me | Theorems.Thm_DistQuantumQuery_proposition_4_8
-- name    : DistQuantumQuery.proposition_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:05.98619+00:00
-- url     : https://prove2.me/theorems/6c375f8e-694d-4c88-a287-13eeb14f00fd
-- title:
--   Proposition 4.8 — $Q(\Phi\to\tilde\Psi)\le\frac2{1-\alpha}\bar\gamma^\mu_2(\Phi-\Psi\mid\{\Delta_i\})$ with fidelity $\ge\alpha$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $\mu$ a distribution, and $\Phi,\Psi\in\mathrm{Pos}(\Sigma)$ Gram matrices with $\Phi\circ I=\Psi\circ I=I$. Then for any $\alpha\in(0,1)$ there is a Gram matrix $\tilde\Psi\in\mathrm{Pos}(\Sigma)$ with $\tilde\Psi\circ I=I$ such that $F(\tilde\Psi\circ|\mu\rangle\langle\mu|,\Psi\circ|\mu\rangle\langle\mu|)\ge\alpha$ and
--   $$
--   Q(\Phi\to\tilde\Psi)\le\frac2{1-\alpha}\,\bar\gamma^\mu_2(\Phi-\Psi\mid\{\Delta_i\}).
--   $$
--   This is the upper-bound half of the $\bar\gamma_2$ characterization of state conversion.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: index register with basis |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential; reason: the same oracle model; Fin (d+1) always contains the start vector
--   - encoding: Q(Φ → Ψ): state families realized in a fixed, sufficiently large realization space V inside the work space → realizations existential in the algorithm's work space Option ι × Fin (d+1); reason: by Corollary 2.7 realizations with equal Gram matrices differ by an input-independent unitary, absorbed into U_0
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Proposition 4.8, p.41

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist
import Definitions.Def_DistQuantumQuery_gammaBar

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Proposition 4.8** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Proposition 4.8, p.41). Let `Σ ⊆ {0,1}^n`, `μ` a distribution and
`Φ, Ψ ∈ Pos(Σ)` Gram matrices with `Φ ∘ I = Ψ ∘ I = I`. Then for any `α ∈ (0,1)` there is a Gram
matrix `Ψ̃ ∈ Pos(Σ)` with `Ψ̃ ∘ I = I` such that `F(Ψ̃ ∘ |μ⟩⟨μ|, Ψ ∘ |μ⟩⟨μ|) ≥ α` and
`Q(Φ → Ψ̃) ≤ (2/(1 − α)) · γ̄^μ₂(Φ − Ψ | {Δ_i})`.

**Formalization Note** The bound is in `ℝ≥0∞`. -/
theorem proposition_4_8 {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (ι → Bool))
    (μ : S → ℝ) (hμ : IsDist μ) (Φ Ψ : Matrix S S ℂ) (hΦ : Φ.PosSemidef) (hΨ : Ψ.PosSemidef)
    (hΦd : Φ ⊙ (1 : Matrix S S ℂ) = 1) (hΨd : Ψ ⊙ (1 : Matrix S S ℂ) = 1)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ Ψt : Matrix S S ℂ, Ψt.PosSemidef ∧ Ψt ⊙ (1 : Matrix S S ℂ) = 1 ∧
      α ≤ fidelity (Ψt ⊙ muMat μ) (Ψ ⊙ muMat μ) ∧
      (QConv S Φ Ψt : ℝ≥0∞) ≤
        ENNReal.ofReal (2 / (1 - α)) * gammaBar μ (Φ - Ψ) (qfilters S) := by sorry

end DistQuantumQuery
