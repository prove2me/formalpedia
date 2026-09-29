-- Prove2me | Theorems.Thm_FamousTheorems_deriv_eq_zero
-- name    : FamousTheorems.deriv_eq_zero
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:44.209366+00:00
-- url     : https://prove2.me/theorems/8e44873e-7cc5-4360-be1a-637fb2ef11bb
-- title:
--   Fermat's theorem on stationary points
-- statement:
--   **Fermat's theorem on stationary points.** At an interior local extremum of a differentiable function, the derivative vanishes. This is the first-derivative test and the foundation of optimisation: it reduces the search for extrema to solving $f' = 0$, turning an analytic problem into an algebraic one. The converse fails — $x^3$ has vanishing derivative at a non-extremum — so stationarity is necessary but not sufficient, which is what the second-derivative test addresses. Interiority is essential, since extrema on a boundary need not be stationary. Fermat's method of *adequality* (c. 1630) predates the formal calculus. **Formalization note.** `IsLocalExtr` covers both local minima and maxima, and the conclusion is about `deriv`. The result is Mathlib's `IsLocalExtr.deriv_eq_zero`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem deriv_eq_zero :
    ∀ {f : ℝ → ℝ} {a : ℝ}, IsLocalExtr f a → deriv f a = 0 := by sorry

end FamousTheorems
