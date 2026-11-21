-- Prove2me | Theorems.Thm_AutoformalisationSCI_dSetL_two_eq_dSet
-- name    : AutoformalisationSCI.dSetL_two_eq_dSet
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T15:33:58.340713+00:00
-- url     : https://prove2.me/theorems/789da5a3-4c51-46e7-bc1e-5547635261ac
-- title:
--   Consistency: $d_2 = d$
-- statement:
--   **Consistency remark** (p. 22). With the same $k$ and the same polynomial enumeration, the case $l=2$ of the predicate $B_e^{(l)}$ is exactly $B_e$, so that $d_2=d$. This recovers Theorem A.3 as the $l=2$ instance of Theorem A.4.
--
--   This is a sanity check that the general level-$l$ construction specialises correctly to the base case.
-- source:
--   A. Bastounis, F. Circelli, A. C. Hansen, Navier–Stokes lost in translation, arXiv:2610.08144 (2026), https://arxiv.org/abs/2610.08144. Paragraph following the proof of Theorem A.4, p. 22 ('the case l = 2 gives B_e^(2)(n) = B_e(n) ... so that d_2 = d').

import Mathlib
import Definitions.Def_AutoformalisationSCI_Poly

open AutoformalisationSCI

namespace AutoformalisationSCI

theorem dSetL_two_eq_dSet (k : ℕ) (E : ComputablePolyEnum (k + 1)) :
    dSetL 2 k (by omega)
        (cast (congrArg ComputablePolyEnum (by omega : k + 1 = 2 - 1 + k)) E) =
      dSet k E := by sorry

end AutoformalisationSCI
