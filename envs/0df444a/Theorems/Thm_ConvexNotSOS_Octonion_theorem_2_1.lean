-- Prove2me | Theorems.Thm_ConvexNotSOS_Octonion_theorem_2_1
-- name    : ConvexNotSOS.Octonion.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:49.341808+00:00
-- url     : https://prove2.me/theorems/a69748c2-095f-4fc3-a14d-aa36503a4534
-- title:
--   Theorem 2.1 — Blekherman’s convexity criterion
-- statement:
--   Let $p$ be a real form of degree $2d$ in finitely many variables, with $d\ge1$. If, at every real vector $z$,
--
--   $$\|z\|^{2d}\left(1-\frac1{2d-1}\right)\le p(z)\le\|z\|^{2d}\left(1+\frac1{2d-1}\right),$$
--
--   then $p$ is convex. This criterion converts a uniform radial bound into convexity and is the input to Lemma 2.2.
--
--   **Formalization Note.** The variable type may be empty; the nonempty condition is needed only by the later bound and SOS statements. The denominator is a real expression, with $d\ge1$.
-- source:
--   Saunderson, A convex form that is not a sum of squares, arXiv:2105.08432v2, p. 4, Theorem 2.1

import Definitions.Def_ConvexNotSOS_Octonion_Forms

namespace ConvexNotSOS.Octonion
open MvPolynomial

theorem theorem_2_1 {σ : Type*} [Fintype σ] (d : ℕ) (hd : 1 ≤ d)
    (p : MvPolynomial σ ℝ) (hp : p.IsHomogeneous (2 * d))
    (hb : ∀ x : σ → ℝ,
      (∑ i : σ, x i ^ 2) ^ d * (1 - 1 / (2 * (d : ℝ) - 1)) ≤ eval x p ∧
      eval x p ≤ (∑ i : σ, x i ^ 2) ^ d * (1 + 1 / (2 * (d : ℝ) - 1))) :
    ConvexOn ℝ Set.univ (fun x : σ → ℝ => eval x p) := by sorry
end ConvexNotSOS.Octonion
