-- Prove2me | Theorems.Thm_Erdos30_lindstrom_upper_bound
-- name    : Erdos30.lindstrom_upper_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T17:45:02.546073+00:00
-- url     : https://prove2.me/theorems/03874d35-3ed9-47ce-b3a3-389cafd329b0
-- title:
--   Erdős–Turán / Lindström: $h(N)\le N^{1/2}+N^{1/4}+1$
-- statement:
--   For every natural number $N$,
--
--   $$h(N)\ \le\ N^{1/2}+N^{1/4}+1.$$
--
--   Erdős and Turán (1941) proved $h(N)\le N^{1/2}+O(N^{1/4})$; Lindström (1969) gave an alternative proof with this explicit bound, and, as noted at erdosproblems.com/30, both proofs in fact give it. Together with Singer's lower bound it shows $h(N)\sim\sqrt N$.
-- source:
--   P. Erdős, P. Turán, On a problem of Sidon in additive number theory, and on some related problems, J. London Math. Soc. 16 (1941), 212–215, https://doi.org/10.1112/jlms/s1-16.4.212 ; B. Lindström, An inequality for B2-sequences, J. Combin. Theory 6 (1969), 211–212, https://doi.org/10.1016/S0021-9800(69)80124-9 ; bound as stated at Erdős Problem #30, https://www.erdosproblems.com/30

import Mathlib
import Definitions.Def_Erdos30Basic

namespace Erdos30

theorem lindstrom_upper_bound (N : ℕ) :
    (h N : ℝ) ≤ Real.sqrt N + (N : ℝ) ^ ((1 : ℝ) / 4) + 1 := by
  sorry

end Erdos30
