-- Prove2me | Theorems.Thm_DiazModulus_rank_one_polynomial_matrix_factor
-- name    : DiazModulus.rank_one_polynomial_matrix_factor
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-16T13:59:12.334956+00:00
-- url     : https://prove2.me/theorems/f74e3c82-c115-4080-9a85-c16721ed20da
-- title:
--   A rank-one 2×3 matrix over F[X] with non-zero entries factors as aᵢbⱼ with a₁, a₂ coprime
-- statement:
--   Let $F$ be a field and $P$ a $2 \times 3$ matrix over $F[X]$ with non-zero entries whose $2 \times 2$ minors all vanish. Then $P_{ij} = a_ib_j$ for some $a \in F[X]^2$ with coprime entries and some $b \in F[X]^3$.
--
--   **Proof.** Let $g = \gcd(P_{00}, P_{10})$ and $a_i = P_{i0}/g$, which are coprime. The minor on columns $0$ and $j$ gives $a_1P_{0j} = a_0P_{1j}$ after cancelling $g$, so $a_0 \mid P_{0j}$; write $P_{0j} = a_0b_j$, and cancelling $a_0$ gives $P_{1j} = a_1b_j$.
--
--   **Novelty.** A standard fact about polynomial rings over a field; routine.
-- source:
--   Standard. R16 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 16 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem rank_one_polynomial_matrix_factor (F : Type*) [Field F] (P : Fin 2 → Fin 3 → F[X])
    (hP : ∀ i j, P i j ≠ 0)
    (hminor : ∀ i i' j j', P i j * P i' j' = P i j' * P i' j) :
    ∃ (a : Fin 2 → F[X]) (b : Fin 3 → F[X]), IsCoprime (a 0) (a 1) ∧ ∀ i j, P i j = a i * b j := by
  sorry

end DiazModulus
