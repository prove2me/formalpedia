-- Prove2me | Theorems.Thm_ConvexNotSOS_Octonion_theorem_4_11
-- name    : ConvexNotSOS.Octonion.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:51.744415+00:00
-- url     : https://prove2.me/theorems/140cf09d-f8a6-406d-ad9e-2d2380007b5f
-- title:
--   Theorem 4.11 — exact SOS threshold at sixteen octonionic columns
-- statement:
--   For the octonionic quartic $q^{\mathbb O}_k$ defined from the Cauchy–Schwarz form, the precise sum-of-squares threshold is
--
--   $$k\ge17\implies q^{\mathbb O}_k\text{ is not SOS},\qquad k\le16\implies q^{\mathbb O}_k\text{ is SOS}.$$
--
--   The two directions distinguish the first non-SOS member of the family from all smaller members. They provide the non-SOS clause of Theorem 1.2.
--
--   **Formalization Note.** The second implication includes $k=0$, when the zero polynomial is SOS; the paper's restriction argument includes this endpoint.
-- source:
--   Saunderson, A convex form that is not a sum of squares, arXiv:2105.08432v2, p. 14, Theorem 4.11; k = 16 decomposition p. 15

import Definitions.Def_ConvexNotSOS_Octonion_Forms

namespace ConvexNotSOS.Octonion
open MvPolynomial

theorem theorem_4_11 :
    (∀ k : ℕ, 17 ≤ k → ¬ IsSumSq (qPoly k)) ∧
    (∀ k : ℕ, k ≤ 16 → IsSumSq (qPoly k)) := by sorry
end ConvexNotSOS.Octonion
