-- Prove2me | Theorems.Thm_ConvexNotSOS_Octonion_theorem_1_2
-- name    : ConvexNotSOS.Octonion.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:56.627986+00:00
-- url     : https://prove2.me/theorems/8da75cd8-f9d8-4ba9-9a32-e4cb511826a1
-- title:
--   Theorem 1.2 — an explicit convex quartic that is not SOS
-- statement:
--   Let $k\ge17$. The octonionic Cauchy–Schwarz form in $16k$ real variables has optimization gap greater than two, and its companion form is a convex quartic form that is not a sum of squares:
--
--   $$\operatorname{gap}(\operatorname{cs}^{\mathbb O}_k)>2,\qquad q^{\mathbb O}_k=\operatorname{cs}^{\mathbb O}_k+\tfrac14(\|x\|^2+\|y\|^2)^2\text{ is convex and not SOS}.$$
--
--   At $k=17$ this gives an explicit example in $272$ variables. The strict gap and the convex non-SOS conclusion are both part of the paper's theorem.
--
--   **Formalization Note.** “Quartic form” is stated as homogeneity of degree four in `MvPolynomial`; “convex” is convexity of its evaluation on all real coordinate vectors; SOS means a finite sum of polynomial squares. The gap uses the Euclidean unit sphere.
-- source:
--   Saunderson, A convex form that is not a sum of squares, arXiv:2105.08432v2, p. 3, Theorem 1.2

import Definitions.Def_ConvexNotSOS_Octonion_Forms

namespace ConvexNotSOS.Octonion
open MvPolynomial

theorem theorem_1_2 (k : ℕ) (hk : 17 ≤ k) :
    2 < gap 2 (csPoly k) ∧
    (qPoly k).IsHomogeneous 4 ∧
    ConvexOn ℝ Set.univ (fun x : Var k → ℝ => eval x (qPoly k)) ∧
    ¬ IsSumSq (qPoly k) := by sorry
end ConvexNotSOS.Octonion
