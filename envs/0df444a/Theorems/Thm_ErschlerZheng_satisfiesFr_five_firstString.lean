-- Prove2me | Theorems.Thm_ErschlerZheng_satisfiesFr_five_firstString
-- name    : ErschlerZheng.satisfiesFr_five_firstString
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T02:10:33.037496+00:00
-- url     : https://prove2.me/theorems/c701e4c5-f6ae-473b-8b81-aeea28ca3ad9
-- title:
--   p. 59, corrected — the string (012)^∞ satisfies Assumption Fr(5) (printed with D = 3)
-- statement:
--   The string $\omega = (\mathbf{012})^\infty$ (`firstString`) satisfies Assumption $(\mathrm{Fr}(5))$ (`SatisfiesFr 5`): for every $k \ge 0$, the block $\omega_{5k} \ldots \omega_{5k+4}$ contains $\mathbf{201}$ or $\mathbf{211}$ as a substring.
--
--   Erschler and Zheng, p. 59, proof of Theorem A: “The first Grigorchuk group is indexed by the string $\omega = (\mathbf{012})^\infty$, which satisfies Assumption $\mathrm{Fr}(D)$ with $D = 3$.”
--
--   $D = 3$ is corrected to $D = 5$: $(\mathbf{012})^\infty$ does not satisfy $(\mathrm{Fr}(3))$ ([`ErschlerZheng.not_satisfiesFr_three_firstString`](https://prove2.me/theorems/832a2a0c-1b93-4137-aa45-ea8b0af37736)). Theorem 8.3 ([`ErschlerZheng.exists_measure_mass_compl_ball_le_and_exp_le_growth_of_satisfiesFr`](https://prove2.me/theorems/1a116650-da25-4d01-b0a9-a02693d2c364)) is stated for every $D$, with rates free of $D$ (p. 34: “The value of $D$ is not important, as long as it is finite.”), so the proof of Theorem A applies it with $D = 5$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 59, (012)^∞ satisfies Fr(5)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem satisfiesFr_five_firstString : SatisfiesFr 5 firstString := by
  sorry

end ErschlerZheng
