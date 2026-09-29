-- Prove2me | Theorems.Thm_CannonFloydParry_CV1_pow_mul_piV1
-- name    : CannonFloydParry.CV1_pow_mul_piV1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:26:28.113748+00:00
-- url     : https://prove2.me/theorems/71c18648-1cad-4bc9-b016-b7f09f4ec350
-- title:
--   Lemma 6.6 — moving $C_n^m$ past $\pi_k$
-- statement:
--   In $V_1$, for integers $0 \le m < n + 2$ and $0 \le k < n$: i) if $m \le k$, $C_n^m\pi_k = \pi_{k-m}C_n^m$; ii) if $m = k + 1$, $C_n^m\pi_k = \pi_0 \cdots \pi_{n-1}C_n^{m+1}$; iii) if $m = k + 2$, $C_n^m\pi_k = \pi_{n-1} \cdots \pi_0C_n^{m-1}$; iv) if $m > k + 2$, $C_n^m\pi_k = \pi_{k+(n+2-m)}C_n^m$.
--
--   **Formalization Note.** Every natural-number subtraction here is non-truncating under its case's hypothesis.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 246, Lemma 6.6

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem CV1_pow_mul_piV1 (k m n : ℕ) (hmn : m < n + 2) (hkn : k < n) :
    (m ≤ k → CV1 n ^ m * piV1 k = piV1 (k - m) * CV1 n ^ m) ∧
      (m = k + 1 → CV1 n ^ m * piV1 k = ((List.range n).map piV1).prod * CV1 n ^ (m + 1)) ∧
      (m = k + 2 → CV1 n ^ m * piV1 k = ((List.range n).reverse.map piV1).prod * CV1 n ^ (m - 1)) ∧
      (k + 2 < m → CV1 n ^ m * piV1 k = piV1 (k + (n + 2 - m)) * CV1 n ^ m) := by
  sorry

end CannonFloydParry
