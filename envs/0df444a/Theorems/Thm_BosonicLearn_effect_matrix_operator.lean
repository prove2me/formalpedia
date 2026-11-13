-- Prove2me | Theorems.Thm_BosonicLearn_effect_matrix_operator
-- name    : BosonicLearn.effect_matrix_operator
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T04:49:48.070243+00:00
-- url     : https://prove2.me/theorems/acc31ba6-e666-4ccc-8ebb-e87d0b795d0b
-- title:
--   An effect matrix with $0\le\langle z,Ez\rangle\le\|z\|^2$ on finite vectors is a positive contraction on $\ell^2(I)$
-- statement:
--   A matrix whose finite quadratic forms lie between $0$ and $\|z\|^2$ is the matrix of a positive contraction on $\ell^2$.
--
--   Let $I$ be any index set and let $E=(E_{ij})_{i,j\in I}$ be a complex matrix such that for every finite set $s\subseteq I$ and every $z\colon I\to\mathbb C$ the quadratic form
--
--   $$
--   q_s(z)=\sum_{i\in s}\sum_{j\in s}\overline{z_i}\,E_{ij}\,z_j
--   $$
--
--   is real and satisfies $0\le q_s(z)\le\sum_{i\in s}|z_i|^2$. Then there is a bounded operator $F$ on $\ell^2(I)$ such that
--
--   1. $\|F\|\le1$;
--   2. $F$ is positive;
--   3. for every $z\in\ell^2(I)$ and every $i\in I$ the series $\sum_jE_{ij}z_j$ converges and equals $(Fz)_i$;
--   4. $\langle e_i,Fe_j\rangle=E_{ij}$ for the standard basis vectors $e_i$.
--
--   Role. The effects of a POVM on a Fock space are specified in this mission through their matrices and the bounds above. This statement turns each effect into an honest bounded operator, which is what is needed to pair effects with trace-class operators, to pass to limits, and to use operator-level results. It is a foundation for `BosonicLearn.fockPOVM_postprocess` and `BosonicLearn.adaptive_scheme_product_povm`.
--
--   **Formalization Note** The hypothesis is exactly the field `effect_form` of a `FockPOVM` at a measurable set. The space $\ell^2(I)$ is `Hilbert I`, that is Mathlib's `lp (fun _ : I => ℂ) 2`; positivity is `ContinuousLinearMap.IsPositive`; clause 3 is a `HasSum`; $e_i$ is `lp.single 2 i 1`. The index set is arbitrary.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. A proved lemma of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5 ("All of our theorems stated in Sec. 1.2 hold for general POVM measurements on n-mode bosonic systems"); makes precise the remark in definition BosonicLearn_FockPOVM that each effect "is a bounded operator between 0 and I"

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters

open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal ComplexOrder

namespace BosonicLearn

/-- **An effect matrix is a bounded positive operator on `ℓ²`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5: "All of our theorems stated in Sec. 1.2 hold for general POVM measurements on n-mode bosonic
systems". This makes precise the remark in the definition `BosonicLearn_FockPOVM` that an effect, given through
its quadratic forms on finitely supported vectors, "is a bounded operator between 0 and I".

Let `E = (E_{ij})` be a matrix indexed by a set `I` such that for every finite `s ⊆ I` and every `z` the form
`∑_{i,j ∈ s} conj(z_i) E_{ij} z_j` is real and lies between `0` and `∑_{i ∈ s} |z_i|²`. Then there is a bounded
operator `F` on `ℓ²(I)` with
1. `‖F‖ ≤ 1`;
2. `F` positive;
3. `(F z)_i = ∑_j E_{ij} z_j` for every `z ∈ ℓ²(I)` and every `i`, the series being convergent;
4. `⟨e_i, F e_j⟩ = E_{ij}` for the standard basis vectors.

**Formalization Note.** The hypothesis is exactly the field `effect_form` of a `FockPOVM` at a measurable set.
`ℓ²(I)` is `Hilbert I`, Mathlib's `lp (fun _ : I => ℂ) 2`; positivity is `ContinuousLinearMap.IsPositive`; clause 3
is a `HasSum`; `e_i` is `lp.single 2 i 1`. The index set is arbitrary. -/
theorem effect_matrix_operator {I : Type} [DecidableEq I] (E : Matrix I I ℂ)
    (hE : ∀ (s : Finset I) (z : I → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2) :
    ∃ F : Hilbert I →L[ℂ] Hilbert I, ‖F‖ ≤ 1 ∧ F.IsPositive ∧
      (∀ (z : Hilbert I) (i : I), HasSum (fun j => E i j * z j) (F z i)) ∧
      ∀ i j, inner ℂ (lp.single 2 i (1 : ℂ) : Hilbert I) (F (lp.single 2 j (1 : ℂ))) = E i j := by sorry

end BosonicLearn
