-- Prove2me | Theorems.Thm_Apery_outer_bound
-- name    : Apery.outer_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T19:09:00.409385+00:00
-- url     : https://prove2.me/theorems/8cd3894f-5d28-4c73-8af2-a4f31bb1640a
-- title:
--   Outer-range bound: $v_p(\Delta_K) \ge 2\sum_{c,i} w^O_{c,i} - \text{rank loss}$
-- statement:
--   **Outer-range bound.** Let $p$ be prime, $p = 2m+1 \ge 7$, and suppose $K = 40n < 3p$, $2K < p^2$, $3n < p$. Then $v_p(\Delta_K)$ is bounded below by twice the sum of the outer weights $w^O$ over the classes (rows $LoC$) minus the rank loss $37n - ((2p + 22n - 3) - (37n - 1))$. This is `outer_bound` of `Apery/Arith/OuterEntryMain.lean` (built on `OuterFrame.lean`, `OuterBasis.lean`, `OuterEntries.lean`); it is the outer-range local exponent of the normaliser `mN` (`Apery.integral_mN`). **Formalization Note** `Δ`, `LoC`, `wO` are platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/OuterEntryMain.lean#L483-L511 (+ OuterFrame.lean, OuterBasis.lean, OuterEntries.lean)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceValToolkit

open Finset Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

namespace Apery

theorem outer_bound {m : ℕ} (hm : 2 * m + 1 = p) (n : ℕ) (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p)
    (hK : 2 * (40 * n) < p ^ 2) (hpN : 3 * n < p) :
    GV p (Δ n) (2 * ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i -
      ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)) := by
  sorry

end Apery
