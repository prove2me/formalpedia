-- Prove2me | Theorems.Thm_BosonicLearn_effect_trace_pairing
-- name    : BosonicLearn.effect_trace_pairing
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T04:58:24.901208+00:00
-- url     : https://prove2.me/theorems/c8a42445-bcde-42d2-919c-646ffc16e6da
-- title:
--   Trace pairing: $\sum_i\sum_jE_{ij}X_{ji}=\sum_a\langle R_a,FL_a\rangle$ for a bounded operator and a nuclear expansion
-- statement:
--   The trace of a bounded operator against a trace-class matrix can be computed along any nuclear expansion, and all the series involved converge.
--
--   Let $I$ be any index set, $E=(E_{ij})_{i,j\in I}$ a complex matrix and $F$ a bounded operator on $\ell^2(I)$ whose coordinates are given by the rows of $E$: for every $z\in\ell^2(I)$ and every $i$, the series $\sum_jE_{ij}z_j$ converges to $(Fz)_i$. Let $X=(X_{ij})$ be a matrix with a nuclear expansion
--
--   $$
--   X_{ij}=\sum_{a\in\mathbb N}L_a(i)\,\overline{R_a(j)},\qquad L_a,R_a\in\ell^2(I),\qquad\sum_a\|L_a\|\,\|R_a\|<\infty .
--   $$
--
--   Then
--
--   1. for every $i\in I$ the series $\sum_jE_{ij}X_{ji}$ converges;
--   2. the series $\sum_i\big(\sum_jE_{ij}X_{ji}\big)$ converges;
--   3. the series $\sum_a\langle R_a,FL_a\rangle$ converges;
--   4. the two sums are equal:
--
--   $$
--   \sum_{i\in I}\sum_{j\in I}E_{ij}X_{ji}=\sum_{a\in\mathbb N}\langle R_a,FL_a\rangle .
--   $$
--
--   Role. The left-hand side of clause 4 is the quantity $\operatorname{Tr}(E\rho)$ that appears in the Born rule of a POVM in this mission, written as an iterated series. The statement shows that it is a genuine convergent sum and rewrites it as an absolutely convergent series of inner products, which is the form in which one can pass to limits, integrate over a parameter, or compare two effects. It is a foundation for `BosonicLearn.fockPOVM_postprocess` and `BosonicLearn.adaptive_scheme_product_povm`.
--
--   **Formalization Note** Convergence is `Summable`, and the two sides of clause 4 are `tsum`s; by clauses 1–3 they are genuine sums and not the default value $0$ that Lean assigns to a divergent series. The hypothesis on $F$ is clause 3 of `BosonicLearn.effect_matrix_operator`. The nuclear expansion is a `NuclearExpansion X` of `Dependency50.P33`. The index set is arbitrary and $X$ need not be positive.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) and `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.4, Eq. (63), p. 35 (outcome likelihoods as Born probabilities); makes precise the remark in definition BosonicLearn_FockPOVM that Tr(E ρ) "is the iterated series ∑ᵢ ∑ⱼ E_ij ρ_ji, which converges absolutely for bounded E and trace-class ρ"

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion)
open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal

namespace BosonicLearn

/-- **Trace pairing of a bounded operator with a trace-class matrix.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.4, Eq. (63), p. 35 (outcome likelihoods are Born probabilities `⟨ϕ|ρ|ϕ⟩ = Tr(|ϕ⟩⟨ϕ| ρ)`). This makes
precise the remark in the definition `BosonicLearn_FockPOVM` that "`Tr(E ρ)` is the iterated series
`∑ᵢ ∑ⱼ E_ij ρ_ji`, which converges absolutely for bounded `E` and trace-class `ρ`".

Let `F` be a bounded operator on `ℓ²(I)` whose coordinates are given by the rows of a matrix `E`,
`(F z)_i = ∑_j E_{ij} z_j`, and let `X` have a nuclear expansion `X_{ij} = ∑_a L_a(i) conj(R_a(j))` with
`∑_a ‖L_a‖‖R_a‖ < ∞`. Then
1. for every `i` the series `∑_j E_{ij} X_{ji}` converges;
2. the series `∑_i (∑_j E_{ij} X_{ji})` converges;
3. the series `∑_a ⟨R_a, F L_a⟩` converges;
4. `∑_i ∑_j E_{ij} X_{ji} = ∑_a ⟨R_a, F L_a⟩`.

**Formalization Note.** Convergence is `Summable` (unconditional); the two sides of clause 4 are `tsum`s, which
by clauses 1–3 are genuine sums and not the default value `0`. The hypothesis on `F` is clause 3 of
`BosonicLearn.effect_matrix_operator`. The left-hand side of clause 4 is the expression in the Born rule
`FockPOVM.law_born`. The index set is arbitrary. -/
theorem effect_trace_pairing {I : Type} (E : Matrix I I ℂ) (F : Hilbert I →L[ℂ] Hilbert I)
    (hF : ∀ (z : Hilbert I) (i : I), HasSum (fun j => E i j * z j) (F z i))
    (X : Matrix I I ℂ) (e : NuclearExpansion X) :
    (∀ i, Summable fun j => E i j * X j i) ∧
    Summable (fun i => ∑' j, E i j * X j i) ∧
    Summable (fun a => inner ℂ (e.right a) (F (e.left a))) ∧
    ∑' i, ∑' j, E i j * X j i = ∑' a, inner ℂ (e.right a) (F (e.left a)) := by sorry

end BosonicLearn
