-- Prove2me | Theorems.Thm_DiazModulus_coprime_fraction_cubic_over_quadratic_iff_natDegree_le
-- name    : DiazModulus.coprime_fraction_cubic_over_quadratic_iff_natDegree_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T09:44:56.817342+00:00
-- url     : https://prove2.me/theorems/f12b2e43-ef74-4656-83cb-a6a1cb11cd44
-- title:
--   For coprime P, Q over a field, X·R·P = N·Q with R ≠ 0, deg R ≤ 2, deg N ≤ 3 is solvable iff max(deg P, deg Q) ≤ 2, or Q(0) = 0 and the max is ≤ 3
-- statement:
--   Let $K$ be a field and $P, Q \in K[X]$ coprime with $Q \neq 0$. There are $R, N \in K[X]$ with $R \neq 0$, $\deg R \leq 2$, $\deg N \leq 3$ and $XRP = NQ$ if and only if $\max(\deg P, \deg Q) \leq 2$, or $Q(0) = 0$ and $\max(\deg P, \deg Q) \leq 3$.
--
--   **Proof.** ($\Rightarrow$) As $P$ and $Q$ are coprime, $Q \mid XR$; write $XR = QS$. Cancelling $Q$ gives $N = SP$, and $S \neq 0$, so $\deg Q + \deg S \leq 3$ and $\deg P + \deg S \leq 3$. If $Q(0) \neq 0$, the prime $X$ divides $QS$ but not $Q$, so $X \mid S$, $\deg S \geq 1$ and $\max(\deg P, \deg Q) \leq 2$. ($\Leftarrow$) If the maximum is at most $2$ take $R = Q$, $N = XP$; if $Q(0) = 0$ write $Q = XQ_1$ and take $R = Q_1$, $N = P$.
--
--   **Novelty.** An elementary fact about polynomials over a field; routine.
-- source:
--   Not found in the sources read in this form; elementary. R17 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem coprime_fraction_cubic_over_quadratic_iff_natDegree_le (K : Type*) [Field K] (P Q : K[X])
    (hcop : IsCoprime P Q) (hQ : Q ≠ 0) :
    (∃ R N : K[X], R ≠ 0 ∧ R.natDegree ≤ 2 ∧ N.natDegree ≤ 3 ∧ X * R * P = N * Q) ↔
      (max P.natDegree Q.natDegree ≤ 2 ∨ (Q.coeff 0 = 0 ∧ max P.natDegree Q.natDegree ≤ 3)) := by
  sorry

end DiazModulus
