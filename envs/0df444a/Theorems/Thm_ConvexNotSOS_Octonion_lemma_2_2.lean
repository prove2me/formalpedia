-- Prove2me | Theorems.Thm_ConvexNotSOS_Octonion_lemma_2_2
-- name    : ConvexNotSOS.Octonion.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:50.116925+00:00
-- url     : https://prove2.me/theorems/3e541a9a-89a6-4d0c-bacc-d0e4710cc14f
-- title:
--   Lemma 2.2 — a convex correction and SOS threshold
-- statement:
--   Let $p$ be a real form of degree $2d$ in $n\ge1$ variables, where $d\ge1$. Suppose real numbers $a,b$ bound it radially: $a\|z\|^{2d}\le p(z)\le b\|z\|^{2d}$ for every $z$. Set $c=da-(d-1)b$. Then
--
--   $$p(z)-c\|z\|^{2d}\quad\text{is convex},$$
--
--   and, if the best SOS lower bound $p^{\mathrm{sos}}_{\min}$ is strictly below $c$, this corrected form is not SOS. The bound formulation is what the proof and the later octonionic application use.
--
--   **Formalization Note.** The source calls the bounds $p_{\min},p_{\max}$, but applies the lemma with bounds that are not the true extrema at $k=1$. They are explicit parameters here. Positive degree and a nonempty variable type exclude total-function edge cases.
-- source:
--   Saunderson, A convex form that is not a sum of squares, arXiv:2105.08432v2, p. 4, Lemma 2.2

import Definitions.Def_ConvexNotSOS_Octonion_Forms

namespace ConvexNotSOS.Octonion
open MvPolynomial

theorem lemma_2_2 {σ : Type*} [Fintype σ] [Nonempty σ] (d : ℕ)
    (hd : 1 ≤ d) (p : MvPolynomial σ ℝ) (hp : p.IsHomogeneous (2 * d))
    (a b : ℝ) (hb : ∀ x : σ → ℝ,
      a * (∑ i : σ, x i ^ 2) ^ d ≤ eval x p ∧
      eval x p ≤ b * (∑ i : σ, x i ^ 2) ^ d) :
    let c := (d : ℝ) * a - ((d : ℝ) - 1) * b
    ConvexOn ℝ Set.univ
      (fun x : σ → ℝ => eval x (p - C c * normSqPoly σ ^ d)) ∧
    (psosMin d p < c → ¬ IsSumSq (p - C c * normSqPoly σ ^ d)) := by sorry
end ConvexNotSOS.Octonion
