-- Prove2me | Theorems.Thm_EssentialCodingTheory_generalized_hamming_bound
-- name    : EssentialCodingTheory.generalized_hamming_bound
-- status  : Proved
-- author  : @chaikon
-- created : 2026-10-14T16:41:43.181744+00:00
-- url     : https://prove2.me/theorems/1c4d5ef3-ce27-4a1a-917d-b2eef07de81b
-- title:
--   Generalized Hamming bound: $k \le n - \log_q \sum_{i \le \lfloor (d-1)/2 \rfloor} \binom{n}{i}(q-1)^i$
-- statement:
--   Let $\alpha$ be a finite alphabet with $q = |\alpha|$ symbols, let $n, d \ge 0$, and let $C \subseteq \alpha^n$ be a code in which any two distinct codewords differ in at least $d$ coordinates. Then the dimension $k = \log_q |C|$ of $C$ satisfies
--
--   $$k \;\le\; n - \log_q \Bigl( \sum_{i=0}^{\lfloor (d-1)/2 \rfloor} \binom{n}{i} (q-1)^i \Bigr).$$
--
--   In particular this holds for every $(n, k, d)_q$ code, i.e. every code of minimum distance exactly $d$. Logarithms are real; the statement imposes no hypothesis $q \ge 2$ or $C \ne \emptyset$, and with the convention $\log_q x = 0$ for $q \le 1$ or $x = 0$ it remains true in those degenerate cases.
-- source:
--   V. Guruswami, A. Rudra, M. Sudan, Essential Coding Theory (web draft), https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf, §1.7, p. 21, Theorem 1.7.2 (Hamming Bound for any d); definitions: code 1.2.1 (p. 5), dimension 1.2.3 (p. 6), Hamming distance 1.3.3 (p. 8), minimum distance 1.4.1 (p. 12), (n,k,d)_q code 1.7.1 (p. 20).

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.SpecialFunctions.Log.Base
open Finset

namespace EssentialCodingTheory
theorem generalized_hamming_bound {α : Type*} [Fintype α] [DecidableEq α] {n d : ℕ}
    (C : Finset (Fin n → α))
    (hC : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) :
    Real.logb (Fintype.card α) C.card ≤
      n - Real.logb (Fintype.card α)
        ((∑ i ∈ range ((d - 1) / 2 + 1), n.choose i * (Fintype.card α - 1) ^ i : ℕ) : ℝ) := by
  sorry
end EssentialCodingTheory
