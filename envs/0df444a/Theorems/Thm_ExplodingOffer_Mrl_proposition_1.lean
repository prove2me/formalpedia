-- Prove2me | Theorems.Thm_ExplodingOffer_Mrl_proposition_1
-- name    : ExplodingOffer.Mrl.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:36.951003+00:00
-- url     : https://prove2.me/theorems/26608173-de21-493d-bc10-a2a18e40f3c1
-- title:
--   Proposition 1, p. 10 — for a fixed size 0 ≤ s ≤ u the shortest acceptable deadline (T − 𝒯(s)/λ)⁺ is optimal, and it decreases in s
-- statement:
--   Let $X$ be a nonnegative continuous random variable with support $[a,b]$ and finite mean, $\lambda > 0$, $T > 0$, $u > 0$. For every offer size $0 \le s \le u$, the responder's shortest acceptable deadline
--   $$t_D^*(s) = \underline{t}_D(s) = \big(T - \mathcal T(s)/\lambda\big)^+$$
--   (with $t_D^*(s) = 0$ when $s \ge b$) is feasible for problem (7) with size $s$, and $\Pi(s, t_D) \le \Pi(s, t_D^*(s))$ for every deadline $t_D$ with $(s, t_D)$ feasible. Moreover, $t_D^*(s)$ is decreasing (weakly) in $s \in [0, u]$.
--
--   This reduces problem (7) to a one-dimensional problem in the offer size.
--
--   **Formalization Note** "Decreasing" is weak (footnote 3, p. 8). Feasibility is the constraint set of (7), which for a fixed $s \in [0,u]$ is that of problem (8).
-- source:
--   Hu & Tang, Size Matters, So Does Duration: The Interplay between Offer Size and Offer Deadline, SSRN preprint 3143414 (version of 2020-05-16), p. 10, Proposition 1

import Mathlib
import Definitions.Def_ExplodingOffer_Mrl_Model

namespace ExplodingOffer.Mrl

open MeasureTheory

theorem proposition_1 {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b)
    {lam T u : ℝ} (hlam : 0 < lam) (hT : 0 < T) (hu : 0 < u) :
    (∀ s : ℝ, 0 ≤ s → s ≤ u →
      Feasible μ b lam T u s (optDeadline μ b lam T s) ∧
      ∀ tD : ℝ, Feasible μ b lam T u s tD →
        surplus μ b lam T u s tD ≤ surplus μ b lam T u s (optDeadline μ b lam T s)) ∧
    AntitoneOn (optDeadline μ b lam T) (Set.Icc 0 u) := by sorry

end ExplodingOffer.Mrl
