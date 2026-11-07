-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_5_3
-- name    : AdaptiveSparsify.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:40.585191+00:00
-- url     : https://prove2.me/theorems/7476a098-e746-4d14-905e-270ae09d42ae
-- title:
--   Lemma 5.3 — a batched halving sequence has length $O(d\log(n+d+\kappa))$
-- statement:
--   Let $A$ be an $n\times d$ matrix with $\|a_i\|_2^2\le\kappa$, $\kappa>0$, and let $H^{(1)},\dots,H^{(Q)}$ be a batched halving sequence (Definition 5.2). Then
--
--   $$Q\le C\,d\log(n+d+\kappa+2)+C$$
--
--   for an absolute constant $C$. Each batch has leverage at least $0.001$, so it decreases $\det((A^{(q)})^\top A^{(q)}+I/\kappa)$ by a constant factor, and this bound is the volume argument behind the number of phases.
--
--   Differences from the source:
--   - reading: Q ≤ Õ(d) → Q ≤ C d log(n + d + κ + 2) + C, with C absolute; reason: the proof ends with O(d log(ndκ)); log(ndκ) vanishes at n = d = κ = 1, while Q = 1 is always allowed
--   - reading: κ implicit → κ > 0; reason: I/κ in the Gram matrix of Definition 5.2 needs κ ≠ 0, and a positive κ is the paper's; the page assumes nothing more of κ
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Definition 5.2 and Lemma 5.3, p.34

import Mathlib
import Definitions.Def_AdaptiveSparsify_Checker

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 5.3**, p.34.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Definition 5.2 and Lemma 5.3, p.34.

"Let A be a matrix such that that ‖a_i‖²₂ ≤ κ, and H^{(1)}, H^{(2)}, …, H^{(Q)} ⊆ [n] be a batched halving
sequence (as defined in Definition 5.2), it holds that Q ≤ Õ(d)."

**Formalization Note.** The proof ends with `Q ≤ O(d log(ndκ))`. It is stated with `log(n + d + κ + 2)` and
an additive constant, because `log(ndκ)` vanishes at `n = d = κ = 1` and `Q = 1` is always allowed.
`κ > 0` is implicit in the Gram matrix `A⊤A + I/κ`; the page assumes nothing more of `κ`. -/
theorem lemma_5_3 : ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ) (κ : ℝ)
    (H : ℕ → Finset (Fin n)) (Q : ℕ),
    0 < κ → (∀ i, A i ⬝ᵥ A i ≤ κ) → IsBatchedHalving κ A H Q →
    (Q : ℝ) ≤ C * ((d : ℝ) * Real.log ((n : ℝ) + d + κ + 2)) + C := by sorry

end AdaptiveSparsify
