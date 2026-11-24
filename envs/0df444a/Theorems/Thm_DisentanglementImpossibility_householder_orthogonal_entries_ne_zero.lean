-- Prove2me | Theorems.Thm_DisentanglementImpossibility_householder_orthogonal_entries_ne_zero
-- name    : DisentanglementImpossibility.householder_orthogonal_entries_ne_zero
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:30:29.379621+00:00
-- url     : https://prove2.me/theorems/0ba7b661-6883-4ddf-a818-cfddd20c9f56
-- title:
--   Theorem 1 (proof, matrix $A$): Householder matrices with no zero entry
-- statement:
--   Let $d\ge2$. For $\alpha\in(0,\tfrac12)$, let $v\in\mathbb{R}^d$ have $v_1=\sqrt\alpha$ and $v_i=\sqrt{(1-\alpha)/(d-1)}$ for $i=2,\dots,d$, and let $A_\alpha=I_d-2vv^\top$. Then $v^\top v=1$, the matrix $A_\alpha$ is orthogonal, and
--
--   $$(A_\alpha)_{ij}\ne0\qquad\text{for all }i,j=1,\dots,d.$$
--
--   Moreover, distinct $\alpha\in(0,\tfrac12)$ give distinct matrices $A_\alpha$, so the construction yields infinitely many such matrices.
--
--   These matrices supply the orthogonal matrices with no zero entry that the proof of Theorem 1 needs.
--
--   **Formalization Note** The paper writes $A_{ij}=-v_iv_j$ for $i\ne j$. The correct value is $-2v_iv_j$, which is also nonzero. The paper's "infinite family of such matrices" is stated as injectivity of $\alpha\mapsto A_\alpha$ on $(0,\tfrac12)$.
-- source:
--   Locatello, Bauer, Lucic, Rätsch, Gelly, Schölkopf, Bachem, Challenging Common Assumptions in the Unsupervised Learning of Disentangled Representations, ICML 2019, arXiv:1811.12359v4, Appendix A (Proof of Theorem 1), Householder construction of A, p. 12

import Mathlib
import Definitions.Def_DisentanglementImpossibility_Basic

open MeasureTheory ProbabilityTheory

namespace DisentanglementImpossibility

theorem householder_orthogonal_entries_ne_zero {d : ℕ} (hd : 1 < d) :
    (∀ α ∈ Set.Ioo (0 : ℝ) (1 / 2),
      (∑ i, householderVec d α i ^ 2 = 1) ∧
      householderMat d α ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      (∀ i j, householderMat d α i j ≠ 0)) ∧
    Set.InjOn (householderMat d) (Set.Ioo (0 : ℝ) (1 / 2)) := by sorry

end DisentanglementImpossibility
