-- Prove2me | Theorems.Thm_DiazModulus_two_sumset_iff_difference_count
-- name    : DiazModulus.two_sumset_iff_difference_count
-- status  : Open
-- author  : @carlok
-- created : 2026-10-08T13:10:30.415984+00:00
-- url     : https://prove2.me/theorems/353f44e5-54a3-4e7c-928f-2a60c3e964ca
-- title:
--   A finite set S of integers contains a sumset A + B with |A| = 2, |B| = q if and only if some difference d > 0 occurs at least q times in S
-- statement:
--   Let $S$ be a finite set of integers and $q \ge 0$. There are $A, B \subseteq \mathbb{Z}$ with $|A| = 2$, $|B| = q$ and $A + B \subseteq S$ if and only if some $d > 0$ has $\#\{s \in S : s + d \in S\} \ge q$.
--
--   With `DiazModulus.laurent_hull_config_iff` it decides when a Laurent hull $\operatorname{span}\{u^s : s \in S\}$ carries a $2 \times 3$ configuration: exactly when some difference occurs three times in $S$.
--
--   **Proof.** If $A = \{a, b\}$ with $a < b$, the translate $B + a$ has $q$ elements $s$ with $s, s + (b - a) \in S$. Conversely, take $B$ of size $q$ inside $\{s \in S : s + d \in S\}$ and $A = \{0, d\}$.
--
--   **Novelty.** Elementary.
-- source:
--   Elementary combinatorics; a step of R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Pointwise in
theorem two_sumset_iff_difference_count (S : Finset ℤ) (q : ℕ) :
    (∃ A B : Finset ℤ, A.card = 2 ∧ B.card = q ∧ A + B ⊆ S) ↔
      ∃ d : ℤ, 0 < d ∧ q ≤ (S.filter (fun s => s + d ∈ S)).card := by
  sorry

end DiazModulus
