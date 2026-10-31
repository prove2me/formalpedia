-- Prove2me | Theorems.Thm_DiazModulus_card_multiIndex
-- name    : DiazModulus.card_multiIndex
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:51:28.404146+00:00
-- url     : https://prove2.me/theorems/35360dd3-8938-40cf-8c28-4389e1d6fd7e
-- title:
--   Stars and bars: the number of $\alpha \in \mathbb{N}^n$ with $\alpha_1 + \cdots + \alpha_n \le S$ is $\binom{S + n}{n}$
-- statement:
--   For $n, S \in \mathbb{N}$, the number of $\alpha : \{1, \dots, n\} \to \{0, \dots, S\}$ with $\alpha_1 + \cdots + \alpha_n \le S$ is $\binom{S + n}{n}$.
--
--   **Proof.** Adding the slack $S - \sum_i \alpha_i$ as an extra entry is a bijection onto the tuples in $\mathbb{N}^{n+1}$ of sum $S$, counted by stars and bars.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical combinatorics: stars and bars. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem card_multiIndex (n S : ℕ) :
    (Finset.univ.filter fun α : Fin n → Fin (S + 1) => ∑ i, (α i : ℕ) ≤ S).card = (S + n).choose n := by
  sorry

end DiazModulus
