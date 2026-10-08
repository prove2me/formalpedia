-- Prove2me | Theorems.Thm_ErschlerZheng_isAdmissibleSeq_kLog_and_kLog_two_eq_and_kLog_three_eq
-- name    : ErschlerZheng.isAdmissibleSeq_kLog_and_kLog_two_eq_and_kLog_three_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:16:29.273432+00:00
-- url     : https://prove2.me/theorems/011081e3-0764-4abc-aca5-5b8139e58296
-- title:
--   Supporting fact for k_n = A⌊log₂ n⌋ (p. 42), not in the paper — for D ⩾ 2 and D | A > 0 it meets the standing assumption of p. 40, and k_2 = k_3 = A
-- statement:
--   Let $D \ge 2$ and $A > 0$ be natural numbers with $D \mid A$. Then the sequence $k_n = A\lfloor\log_2 n\rfloor$ (`kLog A`, where $\lfloor\log_2 n\rfloor$ is `Nat.log 2 n`) satisfies the standing assumption of p. 40 (`IsAdmissibleSeq D (kLog A)`): it is non-decreasing, and $k_n$ is positive and divisible by $D$ for every $n \ge 1$ divisible by $D$. Moreover $k_2 = A$ and $k_3 = A$.
--
--   This is not a result of the paper. It backs two sentences. In the Construction bundle note `ErschlerZheng_Construction`, “Increasing” in the standing assumption of p. 40 is read as non-decreasing because the choice $k_n = A\lfloor\log_2 n\rfloor$ of p. 42 is not strictly increasing ($k_2 = k_3$), and the statement shows that this choice meets the assumption so read. In the note of `isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le` (Corollary 8.2), the choice “exceeds $n$ for small $n$ when $A$ is large”: $k_2 = A$, which exceeds $2$ once $A > 2$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 40, k_n = A⌊log₂ n⌋ is admissible, with k_2 = k_3 = A (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem isAdmissibleSeq_kLog_and_kLog_two_eq_and_kLog_three_eq (D A : ℕ) (hD : 2 ≤ D) (hA : 0 < A)
    (hDA : D ∣ A) :
    IsAdmissibleSeq D (kLog A) ∧ kLog A 2 = A ∧ kLog A 3 = A := by
  sorry

end ErschlerZheng
