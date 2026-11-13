-- Prove2me | Theorems.Thm_BosonicLearn_isDensity_reindex
-- name    : BosonicLearn.isDensity_reindex
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T05:29:18.753019+00:00
-- url     : https://prove2.me/theorems/dc78f31b-d252-444f-995a-544b6ba29a65
-- title:
--   Relabelling the basis along a bijection preserves density operators
-- statement:
--   A density operator remains a density operator when the basis is relabelled.
--
--   Let $X$ be a density operator on $\ell^2(A)$, given by its matrix, and let $e\colon A\to B$ be a bijection of index sets. Then the matrix
--
--   $$
--   X'(i,j)=X\big(e^{-1}(i),e^{-1}(j)\big),\qquad i,j\in B,
--   $$
--
--   is a density operator on $\ell^2(B)$.
--
--   Role. It allows the product basis of a multi-copy system to be indexed in whichever way is convenient, for instance by tuples or by nested pairs.
--
--   **Formalization Note** Density operators are `IsDensity` of `Dependency50.P33`. The index sets are arbitrary.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators), `BosonicLearn.effect_trace_pairing` (Born sums along nuclear expansions), `BosonicLearn.fockPOVM_form_measure` (effects are weakly $\sigma$-additive) and `BosonicLearn.fockPOVM_postprocess`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 4 ("A natural basis for H^{(n)} is the Fock basis {|m⟩ ≡ |m_1⟩ ⊗ ⋯ ⊗ |m_n⟩}")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

namespace BosonicLearn

/-- **Relabelling the basis preserves density operators.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 4: "A natural basis for H^{(n)} is the Fock basis {|m⟩ ≡ |m_1⟩ ⊗ ⋯ ⊗ |m_n⟩}_{m ∈ ℕⁿ}".

If `X` is a density operator on `ℓ²(A)` and `e : A ≃ B` is a bijection of index sets, then the relabelled matrix
`X'(i, j) = X(e⁻¹ i, e⁻¹ j)` is a density operator on `ℓ²(B)`.

**Formalization Note.** Density operators are `IsDensity` of `Dependency50.P33`. The index sets are arbitrary. -/
theorem isDensity_reindex {A B : Type} (e : A ≃ B) {X : Matrix A A ℂ} (hX : IsDensity X) :
    IsDensity (fun i j : B => X (e.symm i) (e.symm j)) := by sorry

end BosonicLearn
