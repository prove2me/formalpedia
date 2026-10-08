-- Prove2me | Theorems.Thm_ErschlerZheng_not_satisfiesFr_three_firstString
-- name    : ErschlerZheng.not_satisfiesFr_three_firstString
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:15:33.025411+00:00
-- url     : https://prove2.me/theorems/832a2a0c-1b93-4137-aa45-ea8b0af37736
-- title:
--   p. 59, as printed, fails — (012)^∞ does not satisfy Assumption Fr(3)
-- statement:
--   The string $(\mathbf{012})^\infty$ (`firstString`), which indexes the first Grigorchuk group, does not satisfy Assumption $(\mathrm{Fr}(3))$ (`SatisfiesFr 3`).
--
--   Erschler and Zheng, p. 59, proof of Theorem A: “The first Grigorchuk group is indexed by the string $\omega = (\mathbf{012})^\infty$, which satisfies Assumption $\mathrm{Fr}(D)$ with $D = 3$.”
--
--   The statement is the negation of this claim as printed. The corrected claim, with $D = 5$, is the milestone `ErschlerZheng.satisfiesFr_five_firstString`; Example 7.10 (p. 41) applies $D = 3$ to the shifted string: “The defining string of $G$ is $(\mathbf{012})^\infty = \mathbf{01}(\mathbf{201})^\infty$, with a shift of two digits it satisfies Assumption $\mathrm{Fr}(D)$, $D = 3$.”
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 59, (012)^∞ satisfies Fr(3), as printed (fails)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem not_satisfiesFr_three_firstString : ¬ SatisfiesFr 3 firstString := by
  sorry

end ErschlerZheng
