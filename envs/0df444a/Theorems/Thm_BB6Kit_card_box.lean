-- Prove2me | Theorems.Thm_BB6Kit_card_box
-- name    : BB6Kit.card_box
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T22:13:03.530911+00:00
-- url     : https://prove2.me/theorems/8ccf06eb-1c4a-4d31-9cde-72f715c39ac4
-- title:
--   Independent $\alpha$'s give $(X+1)(Y+1)(Z+1)$ distinct values $\alpha_1^r\alpha_2^s\alpha_3^t$
-- statement:
--   **Lemma.** If $\alpha_1,\alpha_2,\alpha_3$ are positive and multiplicatively independent, the numbers $\alpha_1^r\alpha_2^s\alpha_3^t$ with $0\le r\le X$, $0\le s\le Y$, $0\le t\le Z$ are pairwise distinct, so there are exactly $(X+1)(Y+1)(Z+1)$ of them. This turns the cardinality conditions (2.10), (2.11) of the Mignotte–Voutier kit into products (their Section 5.1).
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Section 5.1 (cardinality conditions under (5.1)).

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem card_box (α1 α2 α3 X Y Z : ℕ) (h1 : 0 < α1) (h2 : 0 < α2) (h3 : 0 < α3)
    (hind : BB6Kit.MultIndep α1 α2 α3) :
    ((Finset.range (X + 1) ×ˢ Finset.range (Y + 1) ×ˢ Finset.range (Z + 1)).image
      (fun x => α1 ^ x.1 * α2 ^ x.2.1 * α3 ^ x.2.2)).card = (X + 1) * (Y + 1) * (Z + 1) := by
  sorry
end BB6Kit
