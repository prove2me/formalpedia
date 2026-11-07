-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_5_1
-- name    : AdaptiveSparsify.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:29.729209+00:00
-- url     : https://prove2.me/theorems/001072b8-5622-48f7-b986-c51249cf4d65
-- title:
--   Lemma 5.1 — halving a set of leverage at most $1.2$ changes the Gram matrix by at most a factor $10$
-- statement:
--   Let $A$ be an $n\times d$ matrix, $\kappa>0$, and $H$ a set of rows with
--
--   $$\sum_{i\in H}a_i^\top\big(A^\top A+I/\kappa\big)^{-1}a_i-\sum_{i\in H}\big(\tfrac12a_i\big)^\top\big(A^\top A+I/\kappa\big)^{-1}\big(\tfrac12a_i\big)\le0.9.$$
--
--   The Gram matrix after replacing each $a_i$, $i\in H$, by $\tfrac12a_i$ equals $A^\top A-\tfrac34(A_{H,:})^\top A_{H,:}+I/\kappa$, and
--
--   $$\tfrac1{10}\big(A^\top A+I/\kappa\big)\preceq\big(A^\top A-\tfrac34(A_{H,:})^\top A_{H,:}\big)+I/\kappa\preceq A^\top A+I/\kappa.$$
--
--   Batches of bounded leverage therefore keep consecutive Gram matrices comparable, which lets one sparsifier serve the next phase.
--
--   Differences from the source:
--   - reading: κ implicit → κ > 0; reason: I/κ must be a positive multiple of the identity
--   - encoding: the printed hypothesis "at most 1.2, or equivalently … at most 0.9" → the removed-leverage form (≤ 0.9) alone; reason: the two are equal, by ¾ · 1.2 = 0.9
--   - encoding: the middle term of the display → stated for the halved matrix, with its identity to A⊤A − ¾(A_{H,:})⊤A_{H,:} as a conjunct; reason: the page says "the Gram matrix after halving"; both forms are given
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Lemma 5.1, p.33

import Mathlib
import Definitions.Def_AdaptiveSparsify_Checker

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 5.1**, p.33.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Lemma 5.1, p.33.

"Let A be a matrix and H a subset of rows whose total leverage score w.r.t A⊤A + κ⁻¹I is at most 1.2, or
equivalently, the removed leverage score is at most 0.9: ∑_{i∈H} a_i⊤(A⊤A + I/κ)⁻¹a_i − ∑_{i∈H}
(a_i/2)⊤(A⊤A + I/κ)⁻¹(a_i/2) ≤ 0.9, then the Gram matrix after halving the rows in H, aka. replacing each
a_i with ½a_i for all i ∈ H, 10-approximates the one before (1/10)(A⊤A + I/κ) ⪯ (A⊤A − ¾(A_{H,:})⊤A_{H,:}) +
I/κ ⪯ A⊤A + I/κ."

**Formalization Note.** The middle term of the page is stated for the halved matrix, and the identity with
`A⊤A − ¾ (A_{H,:})⊤A_{H,:}` is the first conjunct. -/
theorem lemma_5_1 {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (H : Finset (Fin n)) (κ : ℝ)
    (hκ : 0 < κ)
    (hH : ∑ i ∈ H, leverage (gramOf κ A) (A i) -
        ∑ i ∈ H, leverage (gramOf κ A) ((1 / 2 : ℝ) • A i) ≤ (0.9 : ℝ)) :
    gramOf κ (halve A H) =
      Aᵀ * A - (3 / 4 : ℝ) • (∑ i ∈ H, Matrix.vecMulVec (A i) (A i)) +
        κ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) ∧
    LoewnerLE ((1 / 10 : ℝ) • gramOf κ A) (gramOf κ (halve A H)) ∧
    LoewnerLE (gramOf κ (halve A H)) (gramOf κ A) := by sorry

end AdaptiveSparsify
