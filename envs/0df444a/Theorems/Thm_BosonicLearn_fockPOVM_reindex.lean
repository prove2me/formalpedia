-- Prove2me | Theorems.Thm_BosonicLearn_fockPOVM_reindex
-- name    : BosonicLearn.fockPOVM_reindex
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T05:28:33.845047+00:00
-- url     : https://prove2.me/theorems/21277b49-940c-4be3-9d67-d40a320edc49
-- title:
--   Relabelling the basis of a POVM along a bijection of index sets
-- statement:
--   A POVM can be transported along a relabelling of the basis.
--
--   Let $M$ be a POVM on $\ell^2(J)$ with outcomes in a measurable space $\Omega$ and let $e\colon J\to J'$ be a bijection of index sets. Then there is a POVM $M'$ on $\ell^2(J')$ with outcomes in $\Omega$ such that for every density operator $\rho$ on $\ell^2(J)$ the outcome law of $M'$ on the relabelled operator
--
--   $$
--   \rho'(i,j)=\rho\big(e^{-1}(i),e^{-1}(j)\big),\qquad i,j\in J',
--   $$
--
--   equals the outcome law of $M$ on $\rho$.
--
--   Role. The $N$-copy Fock space has a product basis that can be indexed by $N$-tuples of Fock labels or by nested pairs. This statement passes between the two, as needed when a protocol is built round by round in `BosonicLearn.adaptive_scheme_product_povm`.
--
--   **Formalization Note** Both POVMs are `FockPOVM`s, and density operators are `IsDensity` of `Dependency50.P33`. The index sets are arbitrary.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators), `BosonicLearn.effect_trace_pairing` (Born sums along nuclear expansions), `BosonicLearn.fockPOVM_form_measure` (effects are weakly $\sigma$-additive) and `BosonicLearn.fockPOVM_postprocess`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 4 ("A natural basis for H^{(n)} is the Fock basis {|m⟩ ≡ |m_1⟩ ⊗ ⋯ ⊗ |m_n⟩}"); the N-copy space of Theorem 3, pp. 6–7

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Relabelling the basis of a POVM.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 4: "A natural basis for H^{(n)} is the Fock basis {|m⟩ ≡ |m_1⟩ ⊗ ⋯ ⊗ |m_n⟩}_{m ∈ ℕⁿ}"; the
`N`-copy space has the product basis, which can be indexed by tuples or by nested pairs.

Let `M` be a POVM on `ℓ²(J)` with outcomes in `Ω` and let `e : J ≃ J'` be a bijection of index sets. There is a
POVM `M'` on `ℓ²(J')` with outcomes in `Ω` such that for every density operator `ρ` on `ℓ²(J)` the outcome law of
`M'` on the relabelled operator `ρ'(i, j) = ρ(e⁻¹ i, e⁻¹ j)` is the outcome law of `M` on `ρ`.

**Formalization Note.** Both are `FockPOVM`s. The statement is used to pass between the index types
`(Fin k → ℕⁿ) × ℕⁿ` and `Fin (k + 1) → ℕⁿ` of `k + 1` copies. -/
theorem fockPOVM_reindex {J J' Ω : Type} [DecidableEq J] [DecidableEq J'] [MeasurableSpace Ω]
    (M : FockPOVM J Ω) (e : J ≃ J') :
    ∃ M' : FockPOVM J' Ω, ∀ ρ : Matrix J J ℂ, IsDensity ρ →
      M'.law (fun i j => ρ (e.symm i) (e.symm j)) = M.law ρ := by sorry

end BosonicLearn
