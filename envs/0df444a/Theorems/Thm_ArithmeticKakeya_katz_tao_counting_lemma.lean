-- Prove2me | Theorems.Thm_ArithmeticKakeya_katz_tao_counting_lemma
-- name    : ArithmeticKakeya.katz_tao_counting_lemma
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T21:56:02.678255+00:00
-- url     : https://prove2.me/theorems/e149c95b-14d2-4560-86f7-a015850012ba
-- title:
--   Katz–Tao counting lemma (Lemma 2.1)
-- statement:
--   Katz–Tao's counting lemma: if $f_i:X\to Y_i$ with $|Y_i|\le M_i$ for $1\le i\le k$, then the number of tuples $(x_0,\dots,x_k)\in X^{k+1}$ satisfying $f_i(x_{i-1})=f_i(x_i)$ for all $i$ is at least $|X|^{k+1}/(M_1\cdots M_k)$. Stated in cross-multiplied integer form to avoid division. It lower-bounds the number of copies of a constructible graph inside a set $G$.
-- source:
--   Katz–Tao, Math. Res. Lett. 6 (1999), Lemma 2.1; as stated in https://epoch.ai/frontiermath/open-problems/arithmetic-kakeya

import Mathlib

namespace ArithmeticKakeya
theorem katz_tao_counting_lemma
    (X : Type) [Fintype X] [DecidableEq X]
    (k : ℕ) (Y : Fin k → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (f : (i : Fin k) → X → Y i) (M : Fin k → ℕ)
    (hM : ∀ i, Fintype.card (Y i) ≤ M i) :
    Fintype.card X ^ (k + 1) ≤
      Fintype.card { x : Fin (k + 1) → X // ∀ i : Fin k, f i (x i.castSucc) = f i (x i.succ) } *
        Finset.univ.prod M := by sorry
end ArithmeticKakeya
