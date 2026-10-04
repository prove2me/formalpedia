-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_marginal_nConcave
-- name    : EntropicBarrier.Universal.marginal_nConcave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:03:20.856022+00:00
-- url     : https://prove2.me/theorems/6f5e02ba-29f5-45cd-840a-9aa507e8c61b
-- title:
--   §4, p. 9 — the section marginal $\lambda$ is $n$-concave on its support $(a,b)$
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ be a convex body, $\theta\in\mathbb R^n\setminus\{0\}$, and let $\lambda$ be the one-dimensional marginal of the uniform measure on $\mathcal K$ in the direction $\theta/\|\theta\|$. With
--   $$a=\inf\{s\in\mathbb R:\lambda(s)>0\},\qquad b=\sup\{s\in\mathbb R:\lambda(s)>0\},$$
--   the function $\lambda$ is $n$-concave on $(a,b)$, that is, $\lambda^{1/n}$ is concave on $(a,b)$.
--
--   This is the consequence of the Brunn–Minkowski inequality that drives the proof of Lemma 3.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 9, §4, proof of Lemma 3 (key observation)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_EntropicBarrier_Universal_Marginal

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem marginal_nConcave {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (θ : EuclideanSpace ℝ (Fin n)) (hθ : θ ≠ 0) :
    IsNConcaveOn (n : ℝ)
      (Set.Ioo (sInf {s : ℝ | 0 < marginalDensity K θ s})
        (sSup {s : ℝ | 0 < marginalDensity K θ s}))
      (marginalDensity K θ) := by sorry

end EntropicBarrier.Universal
