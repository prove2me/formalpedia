-- Prove2me | Theorems.Thm_CannonFloydParry_CV1_mul_piV1
-- name    : CannonFloydParry.CV1_mul_piV1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:26:04.129147+00:00
-- url     : https://prove2.me/theorems/4535fc84-5255-48ae-995a-b12a1fc2f8aa
-- title:
--   Lemma 6.5 — moving $C_n$ and its powers past $\pi_k$ and $\pi_0$
-- statement:
--   In $V_1$, for positive integers $k < n$: i) $C_n\pi_k = \pi_{k-1}C_n$; ii) $C_n\pi_0 = \pi_0 \cdots \pi_{n-1}C_n^2$; iii) $C_n^2\pi_0 = \pi_{n-1} \cdots \pi_0C_n$; iv) $C_n^3\pi_0 = \pi_{n-1}C_n^3$.
--
--   **Formalization Note.** $\pi_0 \cdots \pi_{n-1}$ is the product of `(List.range n).map piV1`, and $\pi_{n-1} \cdots \pi_0$ that of the reversed list. Parts ii)–iv) do not involve $k$; the hypotheses force $n \ge 2$, as in the source.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 245, Lemma 6.5

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem CV1_mul_piV1 (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    CV1 n * piV1 k = piV1 (k - 1) * CV1 n ∧
      CV1 n * piV1 0 = ((List.range n).map piV1).prod * CV1 n ^ 2 ∧
      CV1 n ^ 2 * piV1 0 = ((List.range n).reverse.map piV1).prod * CV1 n ∧
      CV1 n ^ 3 * piV1 0 = piV1 (n - 1) * CV1 n ^ 3 := by
  sorry

end CannonFloydParry
