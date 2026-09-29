-- Prove2me | Theorems.Thm_FamousTheorems_exists_hasderivwithinat_eq_of_gt_of_lt
-- name    : FamousTheorems.exists_hasderivwithinat_eq_of_gt_of_lt
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:31.864407+00:00
-- url     : https://prove2.me/theorems/f12b2dde-fc68-423a-a70e-5d2061e47e91
-- title:
--   Darboux's theorem
-- statement:
--   **Darboux's theorem.** A derivative has the intermediate value property, even when it is not continuous. If $f'$ takes two values on an interval it takes every value between them — so a function like the sign function, which skips values, can never be a derivative. This is remarkable because derivatives genuinely can be discontinuous ($x^2\sin(1/x)$ has a derivative discontinuous at $0$), yet they cannot have jump discontinuities. The proof applies the extreme value theorem to an auxiliary function, using the interior extremum criterion rather than continuity of $f'$. Darboux published it in 1875. **Formalization note.** The derivative is `HasDerivWithinAt` on an interval. The result is Mathlib's `exists_hasDerivWithinAt_eq_of_gt_of_lt`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem exists_hasderivwithinat_eq_of_gt_of_lt :
    ∀ {a b : ℝ} {f f' : ℝ → ℝ}, 
    a ≤ b → (∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) → ∀ {m : ℝ}, f' a < m → m < f' b → m ∈ f' '' Ioo a b := by sorry

end FamousTheorems
