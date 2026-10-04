-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_logPartition_moment_inequality
-- name    : EntropicBarrier.Universal.logPartition_moment_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:26:15.498418+00:00
-- url     : https://prove2.me/theorems/a143883d-c299-47b3-a6d0-dc64839146b8
-- title:
--   §4, p. 7 — $\mathbb E_{p_\theta}\langle X-x(\theta),h\rangle^3\le 2(\mathbb E_{p_\theta}\langle X-x(\theta),h\rangle^2)^{3/2}$
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ be a convex body with canonical exponential family $p_\theta$ and mean $x(\theta)$. For all $\theta,h\in\mathbb R^n$,
--   $$\mathbb E_{X\sim p_\theta}\langle X-x(\theta),h\rangle^3\ \le\ 2\left(\mathbb E_{X\sim p_\theta}\langle X-x(\theta),h\rangle^2\right)^{3/2}.$$
--
--   By eqs. (4) and (5) this is the self-concordance inequality (2) for the log-partition function $f$ on $\mathbb R^n$.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 7, §4, display before Lemma 2

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_EntropicBarrier_Universal_ExpFamily

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem logPartition_moment_inequality {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (θ h : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ⟪x - meanMap K θ, h⟫ ^ 3 ∂(expFamily K θ) ≤
      2 * (∫ x, ⟪x - meanMap K θ, h⟫ ^ 2 ∂(expFamily K θ)) ^ ((3 : ℝ) / 2) := by sorry

end EntropicBarrier.Universal
