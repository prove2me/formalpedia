-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_lemma3_local_subgaussian
-- name    : EntropicBarrier.Universal.lemma3_local_subgaussian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:03:44.066973+00:00
-- url     : https://prove2.me/theorems/c62545b7-a388-431c-ad89-c6e895dff1b9
-- title:
--   Lemma 3 — $\rho(y+y_0)=\rho(y_0)\zeta(y)e^{-y^2/(2\sigma^2)}$ on $[-M,M]$ with unimodal $\zeta\in[0,1]$
-- statement:
--   Let $n\ge80$, let $\mathcal K\subset\mathbb R^n$ be a convex body, $\theta\in\mathbb R^n\setminus\{0\}$, and let $\rho$ be the density of $Y=\langle\theta/\|\theta\|,X\rangle$, $X\sim p_\theta$. Assume $\rho$ is $C^\infty$-smooth in the interior of its support. Let $y_0\in\operatorname{argmax}_{y\in\mathbb R}\rho(y)$,
--   $$M=\frac{\sqrt{7n\log(n)}}{\|\theta\|},\qquad \sigma^2=\frac{n}{\|\theta\|^2}\cdot\frac{1}{1-\sqrt{7\log(n)/n}}.$$
--   There exists $\zeta:[-M,M]\to[0,1]$, increasing on $[-M,0]$, decreasing on $[0,M]$, with $\zeta(0)=1$, such that for any $y\in[-M,M]$
--   $$\rho(y+y_0)=\rho(y_0)\,\zeta(y)\exp\left(-\frac{y^2}{2\sigma^2}\right).$$
--
--   This says $Y$ is "locally" sub-Gaussian around its mode, the most technical step of the proof of Theorem 1.
--
--   **Formalization Note** The smoothness of $\rho$ is the paper's own without-loss-of-generality reduction (p. 7: approximate $\mathcal K$ by smooth bodies $\mathcal K_k$); it is carried as an explicit hypothesis, `ContDiffOn ℝ ∞ ρ` on the interior of $\{\rho>0\}$. The range $n\ge80$ is the standing range of Theorem 1, inside whose proof the lemma sits; it guarantees $7\log n<n$, so $\sigma^2>0$. $\zeta$ is a function on $\mathbb R$ constrained only on $[-M,M]$; "increasing/decreasing" are non-strict (`MonotoneOn`, `AntitoneOn`). $\rho$ is the fixed pointwise version of the definition item.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 8, Lemma 3 (proof pp. 8-9); smoothness reduction p. 7

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_EntropicBarrier_Universal_Marginal

open scoped RealInnerProductSpace
open MeasureTheory
open scoped ContDiff

namespace EntropicBarrier.Universal

theorem lemma3_local_subgaussian {n : ℕ} (hn : 80 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (θ : EuclideanSpace ℝ (Fin n)) (hθ : θ ≠ 0)
    (hsmooth : ContDiffOn ℝ ∞ (projDensity K θ) (interior {y | 0 < projDensity K θ y}))
    (y₀ : ℝ) (hy₀ : ∀ y, projDensity K θ y ≤ projDensity K θ y₀) :
    ∃ ζ : ℝ → ℝ,
      (∀ y ∈ Set.Icc (-(Real.sqrt (7 * n * Real.log n) / ‖θ‖))
          (Real.sqrt (7 * n * Real.log n) / ‖θ‖), ζ y ∈ Set.Icc (0 : ℝ) 1) ∧
      MonotoneOn ζ (Set.Icc (-(Real.sqrt (7 * n * Real.log n) / ‖θ‖)) 0) ∧
      AntitoneOn ζ (Set.Icc 0 (Real.sqrt (7 * n * Real.log n) / ‖θ‖)) ∧
      ζ 0 = 1 ∧
      ∀ y ∈ Set.Icc (-(Real.sqrt (7 * n * Real.log n) / ‖θ‖))
          (Real.sqrt (7 * n * Real.log n) / ‖θ‖),
        projDensity K θ (y + y₀) =
          projDensity K θ y₀ * ζ y *
            Real.exp (-y ^ 2 /
              (2 * ((n : ℝ) / ‖θ‖ ^ 2 * (1 / (1 - Real.sqrt (7 * Real.log n / n)))))) := by sorry

end EntropicBarrier.Universal
