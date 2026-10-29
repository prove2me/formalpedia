-- Prove2me | Theorems.Thm_FairProxy_ClosedFormDD_eq_13_bounds
-- name    : FairProxy.ClosedFormDD.eq_13_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:01.152182+00:00
-- url     : https://prove2.me/theorems/acd8851f-0631-41f1-bc21-77a0d2a3fc9d
-- title:
--   Proof of Proposition 7, p. 15 — Fréchet endpoint bounds on every attainable disparity
-- statement:
--   For valid observed marginals with both class probabilities positive, every attainable conditional class-weight function $w\in\mathcal W(\mathcal P_D)$ has demographic disparity between the two Fréchet endpoint expressions:
--
--   $$
--   \mu(a;w^L)-\mu(b;w^U)\le\mu(a;w)-\mu(b;w)
--   \le\mu(a;w^U)-\mu(b;w^L).
--   $$
--
--   The lower inequality appears after equation (13) in the proof of Proposition 7; the paper says the upper inequality follows analogously. This gives containment of the identified set in the proposed interval.
--
--   **Formalization Note** The result includes both inequalities, with the group masses positive so $\mu$ has its intended probabilistic meaning.
-- source:
--   Kallus, Mao & Zhou, Assessing Algorithmic Fairness with Unobserved Protected Class Using Data Combination, arXiv:1906.00285v2, p. 15, proof of Proposition 7, after Eq. (13)

import Mathlib
import Definitions.Def_FairProxy_ClosedFormDD_Model

namespace FairProxy.ClosedFormDD

/-- The lower bound in the proof of Proposition 7, p. 15, after equation (13),
and its stated analogous upper bound. -/
theorem eq_13_bounds {Z : Type*} [MeasurableSpace Z]
    (M : Marginals Z) (hM : M.Valid)
    (ha : 0 < probA M .a) (hb : 0 < probA M .b)
    (w : Cls → Fin 2 → Z → ℝ) (hw : w ∈ WPD M) :
    mu M .a (wL M) - mu M .b (wU M) ≤ mu M .a w - mu M .b w ∧
      mu M .a w - mu M .b w ≤
        mu M .a (wU M) - mu M .b (wL M) := by sorry

end FairProxy.ClosedFormDD
