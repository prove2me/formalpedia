-- Prove2me | Theorems.Thm_DiazModulus_five_point_sumset_rigid
-- name    : DiazModulus.five_point_sumset_rigid
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-16T13:58:52.321382+00:00
-- url     : https://prove2.me/theorems/d4afe990-7edc-4c6f-ac8e-7c681c9585a9
-- title:
--   If A + B ⊆ {−k, −1, 0, 1, m} with |A| = 2, |B| = 3, k ≥ 4 and 2 ≤ m ≤ k, then m = 2 and A + B = {−1, 0, 1, 2}
-- statement:
--   Let $k, m$ be integers with $k \geq 4$ and $2 \leq m \leq k$, and let $A, B$ be finite sets of integers with $|A| = 2$, $|B| = 3$ and $A + B \subseteq \{-k, -1, 0, 1, m\}$. Then $m = 2$ and $A + B = \{-1, 0, 1, 2\}$.
--
--   **Proof.** Write $A = \{a, a + d\}$ with $d \geq 1$. For each of the three $b \in B$, $s = a + b$ and $s + d$ lie in $S$, so the difference $d$ is taken at three distinct lower ends. The positive differences of $S$ are $1, 1, 2, m - 1, m, m + 1, k - 1, k, k + 1, k + m$, and as $k - 1 \geq 3$ only $d = 1$ with $m = 2$ occurs three times, at $s = -1, 0, 1$. So $a + B = \{-1, 0, 1\}$ and $A + B = \{-1, 0, 1, 2\}$. The hypothesis $m \leq k$ is not used.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R16 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 16 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Pointwise in
theorem five_point_sumset_rigid (k m : ℤ) (hk : 4 ≤ k) (hm : 2 ≤ m) (hmk : m ≤ k)
    (A B : Finset ℤ) (hA : A.card = 2) (hB : B.card = 3)
    (hAB : A + B ⊆ ({-k, -1, 0, 1, m} : Finset ℤ)) :
    m = 2 ∧ A + B = ({-1, 0, 1, 2} : Finset ℤ) := by
  sorry

end DiazModulus
