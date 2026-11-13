-- Prove2me | Theorems.Thm_BosonicLearn_fockPOVM_form_measure
-- name    : BosonicLearn.fockPOVM_form_measure
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T05:06:03.706203+00:00
-- url     : https://prove2.me/theorems/c4f18403-a54f-4845-95d7-6eb99897a4d6
-- title:
--   Effects of a POVM are weakly $\sigma$-additive: quadratic forms and matrix entries are given by finite measures
-- statement:
--   The effects of a POVM are weakly $\sigma$-additive: their quadratic forms on finitely supported vectors are finite measures, and their matrix entries are complex combinations of four finite measures.
--
--   Let $I$ be an index set and let $P$ be a POVM on $\ell^2(I)$ with outcomes in a measurable space $\Omega$, with effects $E(B)$ for measurable $B\subseteq\Omega$.
--
--   1. For every finite set $s\subseteq I$ and every $z\colon I\to\mathbb C$ there is a finite measure $m$ on $\Omega$ such that for all measurable $B$
--
--   $$
--   \sum_{i\in s}\sum_{j\in s}\overline{z_i}\,E(B)_{ij}\,z_j=m(B).
--   $$
--
--   2. For all $i,j\in I$ there are four finite measures $m_0,m_1,m_2,m_3$ on $\Omega$ such that for all measurable $B$
--
--   $$
--   E(B)_{ij}=\tfrac14\Big[\big(m_0(B)-m_1(B)\big)-\mathrm i\,\big(m_2(B)-m_3(B)\big)\Big].
--   $$
--
--   Role. The definition of a POVM used in this mission lists bounds on the effects, normalization and the Born rule, but no additivity of $B\mapsto E(B)$. This statement supplies it. Consequences used elsewhere are: $E(B)+E(B^{\mathrm c})=\mathbf 1$ entrywise; monotonicity of the quadratic forms in $B$; measurability of $t\mapsto E(A_t)_{ij}$ for a monotone family of sets $A_t$; and the possibility of integrating a bounded function against the entries of $E$. It is a foundation for `BosonicLearn.fockPOVM_postprocess` and `BosonicLearn.adaptive_scheme_product_povm`.
--
--   **Formalization Note** $P$ is a `FockPOVM`. Measures take values in $[0,\infty]$ and $m(B)$ enters the identities through `ENNReal.toReal`. The four measures of clause 2 are indexed by `Fin 4`.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) and `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5 ("general POVM measurements on n-mode bosonic systems"), continuous-outcome POVMs in §5.4, pp. 34–35; makes precise the remark in definition BosonicLearn_FockPOVM that "the effects are weakly σ-additive: this is the usual definition of a POVM"

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM

open MeasureTheory
open scoped ENNReal

namespace BosonicLearn

/-- **The effects of a POVM are weakly σ-additive: quadratic forms and matrix entries are given by finite
measures.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5 ("general POVM measurements on n-mode bosonic systems"); continuous-outcome POVMs are used in
§5.4, pp. 34–35 (`∫ dz_t |ϕ⟩⟨ϕ| = P_k`). This makes precise the remark in the definition `BosonicLearn_FockPOVM`
that "the effects are weakly σ-additive: this is the usual definition of a POVM".

Let `P` be a POVM on `ℓ²(I)` with outcomes in a measurable space `Ω` and effects `E(B)`.
1. For every finite `s ⊆ I` and every `z`, there is a finite measure `m` on `Ω` with
   `∑_{i,j ∈ s} conj(z_i) E(B)_{ij} z_j = m(B)` for all measurable `B`.
2. For all `i, j` there are four finite measures `m₀, m₁, m₂, m₃` on `Ω` with
   `E(B)_{ij} = ¼ [(m₀(B) − m₁(B)) − i (m₂(B) − m₃(B))]` for all measurable `B`.

**Formalization Note.** `P` is a `FockPOVM`, whose fields do not include additivity of the effects; additivity is
derived here from the Born rule on rank-one densities with finite support. Measures take values in `ℝ≥0∞`, and
`m(B)` enters the identities through `ENNReal.toReal`. Clause 2 is clause 1 for the four vectors
`e_i + c e_j`, `c ∈ {1, −1, i, −i}`, by polarization. -/
theorem fockPOVM_form_measure {I Ω : Type} [DecidableEq I] [MeasurableSpace Ω] (P : FockPOVM I Ω) :
    (∀ (s : Finset I) (z : I → ℂ), ∃ m : Measure Ω, IsFiniteMeasure m ∧ ∀ B, MeasurableSet B →
      ∑ i ∈ s, ∑ j ∈ s, star (z i) * P.effect B i j * z j = ((m B).toReal : ℂ)) ∧
    (∀ i j : I, ∃ m : Fin 4 → Measure Ω, (∀ k, IsFiniteMeasure (m k)) ∧ ∀ B, MeasurableSet B →
      P.effect B i j = (1 / 4 : ℂ) * ((((m 0 B).toReal - (m 1 B).toReal : ℝ) : ℂ) -
        Complex.I * (((m 2 B).toReal - (m 3 B).toReal : ℝ) : ℂ))) := by sorry

end BosonicLearn
