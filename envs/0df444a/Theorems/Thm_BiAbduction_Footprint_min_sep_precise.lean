-- Prove2me | Theorems.Thm_BiAbduction_Footprint_min_sep_precise
-- name    : BiAbduction.Footprint.min_sep_precise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:43.919805+00:00
-- url     : https://prove2.me/theorems/d55762ef-ba5d-419a-9854-2aeeca374899
-- title:
--   Proof of Thm 4.11 — for precise P, min(P ∗ X) = min(P) ∗ min(X) and min(P) = P
-- statement:
--   Let $P$ be a precise predicate (Definition 4.9). Then for every predicate $X$,
--   $$\min(P * X) = \min(P) * \min(X), \qquad\text{and}\qquad \min(P) = P.$$
--
--   These are the two steps of the displayed chain in the proof of Theorem 4.11 that the paper attributes to "precision of $P_\alpha$": with $X = Q_\alpha \mathbin{-\!\!*} (P_C * \mathsf{true})$ they rewrite $\min(P_\alpha * X)$ as $P_\alpha * \min(X)$.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 50, §4.2.4, proof of Theorem 4.11 (displayed chain)

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics
import Definitions.Def_BiAbduction_Footprint_Footprint

namespace BiAbduction.Footprint

/-- Proof of Theorem 4.11 (p. 50), the two steps "from precision of `Pα`": if `P` is precise
then `min(P ∗ X) = min(P) ∗ min(X)` for every predicate `X`, and `min(P) = P`. -/
theorem min_sep_precise (P : Pred) (hP : IsPrecise P) :
    (∀ X : Pred, minSet (sepConj P X) = sepConj (minSet P) (minSet X)) ∧
    minSet P = P := by sorry

end BiAbduction.Footprint
