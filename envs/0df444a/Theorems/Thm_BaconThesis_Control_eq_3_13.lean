-- Prove2me | Theorems.Thm_BaconThesis_Control_eq_3_13
-- name    : BaconThesis.Control.eq_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:58:12.968893+00:00
-- url     : https://prove2.me/theorems/ba08d00d-f064-4a84-afcd-ff5ebfeee1f4
-- title:
--   (3.13) — commuting density operators have orthogonal purifications (corrected: finite family)
-- statement:
--   Let $(\rho_i)_{i\in\iota}$ be a finite family of density operators on the apparatus space $\mathcal H_A = \mathbb C^a$ that commute pairwise, $\rho_i\rho_j = \rho_j\rho_i$. Then with the auxiliary system $\mathcal H_R = \mathbb C^{a\times\iota}$ there are vectors $|i\rangle\in\mathcal H_A\otimes\mathcal H_R$ with
--   $$
--   \rho_i = \mathrm{Tr}_R\big[|i\rangle\langle i|\big]\quad\text{for every } i,\qquad \langle i|j\rangle = 0\quad\text{for } i\neq j .
--   $$
--   Each $|i\rangle$ is a unit vector, since $\mathrm{Tr}\,\rho_i = 1$.
--
--   Orthogonal purification is the step that reduces mixed state stationary control to the pure state criterion.
--
--   **Formalization Note** The partial trace over $R$ is the published `WildeQIT.partialTraceRight` (apparatus first).
--
--   Differences from the source:
--   - correction: purifications of every commuting set of ρ_a → a finite family; reason: the printed claim is false for infinite sets in the book's finite-dimensional framework: the set of all diagonal qubit density matrices commutes, but a finite-dimensional A ⊗ R holds only finitely many pairwise orthogonal unit vectors
--   - generalization: some auxiliary system R → the explicit R = ℂ^{a × ι} of dimension dim A · |ι|; reason: exhibiting one R implies the existence the book asserts
--   - generalization: a set of states → an indexed family, and indices i ≠ j get orthogonal purifications even when ρ_i = ρ_j; reason: a set is the family indexed by itself, so the book's case is an instance
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §3.2.2, eq. (3.13), p.34 (PDF p.51)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_IsDensityOperator

open scoped Matrix

namespace BaconThesis.Control

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§3.2.2, eq. (3.13), p.34 (PDF p.51): "Let us introduce an auxiliary system R such that the
purifications of the commuting ρa are orthogonal: ρa = TrR[|a⟩⟨a|], (3.13) where the |a⟩ are
orthogonal. It is always possible to perform such an orthogonal purification when the ρa
commute". For a finite family `(ρ_i)_{i ∈ ι}` of pairwise commuting density operators on `ℂ^a`
there are vectors `|i⟩` on `ℂ^a ⊗ ℂ^R`, with `R = a × ι`, such that `ρ_i = Tr_R[|i⟩⟨i|]` for every
`i` and `⟨i|j⟩ = 0` for `i ≠ j`.

**Formalization Note.** The auxiliary system is the explicit `R = a × ι` (dimension `dim A · |ι|`);
the apparatus is the first tensor factor and `Tr_R` is `WildeQIT.partialTraceRight`. The family is
finite: in finite dimensions infinitely many nonzero vectors cannot be pairwise orthogonal.
Indices `i ≠ j` with `ρ_i = ρ_j` still get orthogonal purifications. Each `|i⟩` is a unit vector,
since `Tr ρ_i = 1`. -/
theorem eq_3_13 {a ι : Type} [Fintype a] [DecidableEq a] [Fintype ι]
    (ρ : ι → Matrix a a ℂ) (hρ : ∀ i, WildeQIT.IsDensityOperator (ρ i))
    (hcomm : ∀ i j, ρ i * ρ j = ρ j * ρ i) :
    ∃ v : ι → (a × (a × ι)) → ℂ,
      (∀ i, WildeQIT.partialTraceRight (Matrix.vecMulVec (v i) (star (v i))) = ρ i) ∧
      ∀ i j, i ≠ j → star (v i) ⬝ᵥ v j = 0 := by sorry

end BaconThesis.Control
