-- Prove2me | Theorems.Thm_Apery_inner_bound_cap
-- name    : Apery.inner_bound_cap
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T19:07:48.603979+00:00
-- url     : https://prove2.me/theorems/1448e693-cae6-4b82-834c-fb6125ad2fed
-- title:
--   Inner-range bound: $v_p(\Delta_K) \ge 2\sum_s w^{\mathrm{cap}}_s$ under the water-filling side conditions
-- statement:
--   **Inner-range bound with capped weights.** Let $p$ be prime, $p = 2m+1$, $m \ge 1$, $p \ge 5$, and let $L : \mathrm{Fin}(m+1) \to \mathbb{N}$ be a class allocation with $\sum_c L_c = 37n$, separating $p$ from the poles $S_p(40n)$, with the degree and water-filling side conditions. Then $v_p(\Delta_K) \ge 2\sum_s w^{\mathrm{cap}}_s$ for the capped weights of the allocation. This is `inner_bound_cap` of `Apery/Arith/InnerWeights.lean` (the `class_frame` plus the capped-weight bookkeeping `InnerAlloc.lean`); it is the inner-range local exponent of the normaliser `mN` (`Apery.integral_mN`). **Formalization Note** `Δ`, `Sep`, `PlK`, `Bse`, `tmin`, `wcap` are platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/InnerWeights.lean#L178-L230 (+ ClassFrame.lean, ClassCount.lean, InnerAlloc.lean)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceValToolkit

open Finset Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

namespace Apery

theorem inner_bound_cap {m : ℕ} (hp5 : 5 ≤ p) (hm : 2 * m + 1 = p) (hm1 : 1 ≤ m)
    (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (hsep : Sep p (PlK (40 * n))) (hK : 40 * n < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (hZ : tmin hm1 L (Bse p (40 * n) (3 * n)) ≤
      2 * L 0 + (Bse p (40 * n) (3 * n) 0 - 4) / 2) :
    GV p (Δ n) (2 * ∑ s, wcap hm1 L (Bse p (40 * n) (3 * n)) s) := by
  sorry

end Apery
