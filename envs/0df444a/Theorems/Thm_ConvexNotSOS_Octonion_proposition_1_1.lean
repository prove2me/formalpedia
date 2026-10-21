-- Prove2me | Theorems.Thm_ConvexNotSOS_Octonion_proposition_1_1
-- name    : ConvexNotSOS.Octonion.proposition_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:57.092998+00:00
-- url     : https://prove2.me/theorems/8b7f6048-6645-4170-90fc-52d09001512a
-- title:
--   Proposition 1.1 — a gap above the degree gives a convex non-SOS form
-- statement:
--   Let $p$ be a degree-$2d$ real form in $n\ge1$ variables, with $d\ge1$, satisfying $p_{\min}\|z\|^{2d}\le p(z)\le p_{\max}\|z\|^{2d}$ for every $z$. If $\operatorname{gap}(p)>d$, then with $c=dp_{\min}-(d-1)p_{\max}$,
--
--   $$p(z)-c\|z\|^{2d}$$
--
--   is convex and is not a sum of squares. This proposition connects the sphere-optimization gap to the convex versus SOS separation.
--
--   **Formalization Note.** The extrema are computed from $p$, and the radial sandwich is included explicitly as in the printed proposition. The real gap quotient is used only under a strict gap hypothesis.
-- source:
--   Saunderson, A convex form that is not a sum of squares, arXiv:2105.08432v2, p. 2, Proposition 1.1; proof p. 4

import Definitions.Def_ConvexNotSOS_Octonion_Forms

namespace ConvexNotSOS.Octonion
open MvPolynomial

theorem proposition_1_1 {σ : Type*} [Fintype σ] [Nonempty σ] (d : ℕ)
    (hd : 1 ≤ d) (p : MvPolynomial σ ℝ) (hp : p.IsHomogeneous (2 * d))
    (hb : ∀ x : σ → ℝ,
      pmin p * (∑ i : σ, x i ^ 2) ^ d ≤ eval x p ∧
      eval x p ≤ pmax p * (∑ i : σ, x i ^ 2) ^ d)
    (hg : (d : ℝ) < gap d p) :
    let c := (d : ℝ) * pmin p - ((d : ℝ) - 1) * pmax p
    ConvexOn ℝ Set.univ
      (fun x : σ → ℝ => eval x (p - C c * normSqPoly σ ^ d)) ∧
    ¬ IsSumSq (p - C c * normSqPoly σ ^ d) := by sorry
end ConvexNotSOS.Octonion
