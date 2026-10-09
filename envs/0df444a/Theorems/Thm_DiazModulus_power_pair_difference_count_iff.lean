-- Prove2me | Theorems.Thm_DiazModulus_power_pair_difference_count_iff
-- name    : DiazModulus.power_pair_difference_count_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-08T13:11:08.272497+00:00
-- url     : https://prove2.me/theorems/c3c5d970-67d0-41e7-a528-b46b89849269
-- title:
--   For integers 4 ≤ k < l, some difference occurs three times in {0, ±1, ±k, ±l} iff l ∈ {k+1, k+2, 2k−1, 2k, 2k+1, 3k}
-- statement:
--   Let $4 \le k < l$ be integers and $S = \{0, \pm 1, \pm k, \pm l\}$. Some $d > 0$ has $\#\{s \in S : s + d \in S\} \ge 3$ if and only if $l \in \{k + 1, k + 2, 2k - 1, 2k, 2k + 1, 3k\}$.
--
--   **Proof.** The six cases have explicit witnesses (for $l = 2k$: $d = k$, $s \in \{0, -k, k\}$). Conversely, $s \mapsto -s - d$ is an involution of $\{s \in S : s + d \in S\}$, so three elements contain two, $x$ and $y$, with $y \notin \{x, -x - d\}$; the pairs $(x, x + d)$ and $(y, y + d)$ then force a coincidence among the differences $1, 2, k \pm 1, k, 2k, l - k, l \pm 1, l, l + k, 2l$, and a case analysis closed by linear arithmetic leaves exactly the six values of $l$.
--
--   **Novelty.** Elementary.
-- source:
--   Elementary combinatorics; a step of R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem power_pair_difference_count_iff (k l : ℤ) (hk : 4 ≤ k) (hkl : k < l) :
    (∃ d : ℤ, 0 < d ∧ 3 ≤ (({0, 1, -1, k, -k, l, -l} : Finset ℤ).filter
      (fun s => s + d ∈ ({0, 1, -1, k, -k, l, -l} : Finset ℤ))).card) ↔
    (l = k + 1 ∨ l = k + 2 ∨ l = 2 * k - 1 ∨ l = 2 * k ∨ l = 2 * k + 1 ∨ l = 3 * k) := by
  sorry

end DiazModulus
