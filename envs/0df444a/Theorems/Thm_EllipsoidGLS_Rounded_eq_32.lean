-- Prove2me | Theorems.Thm_EllipsoidGLS_Rounded_eq_32
-- name    : EllipsoidGLS.Rounded.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:23:20.249202+00:00
-- url     : https://prove2.me/theorems/0c72d187-d37d-4a2f-ac9a-aa8c7a2f41f0
-- title:
--   Proof of Theorem (2.4), (32), p. 176 — µ(K_N) ≤ µ(E_N) ≤ e^{−N/4n} µ(E₀) = e^{−N/4n} RⁿV_n
-- statement:
--   Let $n\ge 2$, let $(K,a_0,r,R)$ be a compact convex body in $\mathbb{R}^n$, let $c\in\mathbb{R}^n$ and $\varepsilon>0$ satisfy $\varepsilon<r$, $\|c\|\ge1$, and assume $R\ge1$, $\varepsilon\le1$. Let $(x_k,A_k)$ be any run of the rounded ellipsoid method for
--   $$N = 4n^2\left\lceil \log\frac{2R^2\|c\|}{r\varepsilon}\right\rceil$$
--   steps with $\delta=R^24^{-N}/(300n)$ and $p=5N$, with ellipsoids $E_k$ and retained sets $K_k$ as in Lemma (2.3). Let $\mu$ be Lebesgue measure and $V_n$ the volume of the Euclidean unit ball of $\mathbb{R}^n$. Then
--   $$\mu(K_N)\le\mu(E_N)\le e^{-N/(4n)}\,\mu(E_0)=e^{-N/(4n)}\,R^nV_n .$$
--
--   This is the upper half of the volume squeeze that closes the proof of Theorem (2.4): after $N$ steps the retained set $K_N$ has exponentially small volume.
--
--   **Formalization Note** The three relations are stated separately in $[0,\infty]$. The middle inequality is stated with the page's rate $e^{-N/(4n)}$, which is stronger than what iterating Lemma (2.2) gives ($e^{-N/(5n)}$); the page's "Lemmas (2.2) and (2.3) imply" is a gap, but the rate $e^{-N/(4n)}$ holds: the per-step volume ratio of the inflated update is $\left(\frac{2n^2+3}{2n^2}\right)^{n/2}\sqrt{\frac{n-1}{n+1}}<e^{-1/(4n)}$ for $n\ge2$, and the rounding perturbation is far smaller than the margin. The final step of the paper's proof needs this rate. The hypotheses $R\ge1$ and $\varepsilon\le1$ are added for the reasons given in Lemmas (2.1) and (2.3). $A_N$ is positive definite by Lemma (2.1), a consequence of the hypotheses.
-- source:
--   Grötschel, Lovász, Schrijver, The ellipsoid method and its consequences in combinatorial optimization, Combinatorica 1 (1981), p. 176, proof of Theorem (2.4), (32)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_EllipsoidGLS_Rounded_Basic
import Definitions.Def_EllipsoidGLS_Rounded_Run

namespace EllipsoidGLS.Rounded

open Matrix

theorem eq_32
    {n : ℕ} (hn : 2 ≤ n) (K : Set (Fin n → ℝ)) (a₀ c : Fin n → ℝ) (r R ε : ℝ)
    (hK : IsConvexBody K a₀ r R) (hc : 1 ≤ euclNorm c) (hε : 0 < ε) (hεr : ε < r)
    (hR : 1 ≤ R)
    (hε1 : ε ≤ 1)
    (N : ℕ) (hN : N = itN n R r ε c)
    (x : ℕ → Fin n → ℝ) (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (feas : ℕ → Prop)
    (a d : ℕ → Fin n → ℝ)
    (hrun : IsRoundedRun K c a₀ R (itDelta n N R) (itP N) N x A feas a d) :
    MeasureTheory.volume (Kk K c x feas N) ≤
        MeasureTheory.volume (LinearOptimization.ellipsoid (x N) (A N)) ∧
      MeasureTheory.volume (LinearOptimization.ellipsoid (x N) (A N)) ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) / (4 * (n : ℝ)))) *
          MeasureTheory.volume (LinearOptimization.ellipsoid (x 0) (A 0)) ∧
      MeasureTheory.volume (LinearOptimization.ellipsoid (x 0) (A 0)) =
        ENNReal.ofReal (R ^ n * unitBallVol n) := by sorry

end EllipsoidGLS.Rounded
