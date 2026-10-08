-- Prove2me | Theorems.Thm_EllipsoidGLS_Rounded_lemma_2_2
-- name    : EllipsoidGLS.Rounded.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:23:01.096889+00:00
-- url     : https://prove2.me/theorems/f8b28f14-e5b3-44a2-95e1-0bb89f437519
-- title:
--   Lemma (2.2), p. 175 — each step shrinks the volume: µ(E_{k+1})/µ(E_k) < e^{−1/5n}
-- statement:
--   Let $n\ge 2$, let $(K,a_0,r,R)$ be a compact convex body in $\mathbb{R}^n$, let $c$ and $\varepsilon>0$ satisfy $\varepsilon<r$, $\|c\|\ge1$, assume $R\ge1$, and let $(x_k,A_k)$ be any run of the rounded ellipsoid method for
--   $$N = 4n^2\left\lceil \log\frac{2R^2\|c\|}{r\varepsilon}\right\rceil$$
--   steps with $\delta=R^24^{-N}/(300n)$ and $p=5N$. Write
--   $$E_k=\{x\in\mathbb{R}^n : (x-x_k)^{\mathsf T}A_k^{-1}(x-x_k)\le 1\}$$
--   and let $\mu$ be the $n$-dimensional (Lebesgue) volume. Then for every $k<N$
--   $$\mu(E_{k+1}) < e^{-1/(5n)}\,\mu(E_k).$$
--
--   Iterated over the $N$ steps, this geometric shrinkage of the ellipsoids is what forces the retained part of the body to be thin in the direction of $c$.
--
--   **Formalization Note** The ratio $\mu(E_{k+1})/\mu(E_k)$ of the page is stated multiplicatively in $[0,\infty]$; both volumes are finite and positive because $A_k$, $A_{k+1}$ are positive definite by Lemma (2.1), which is a consequence of the hypotheses and not an extra assumption. $E_k$ is the published `LinearOptimization.ellipsoid`. The hypothesis $R\ge1$ is added for the reason given in Lemma (2.1): without it the rounding can make $A_{k+1}$ singular, in which case Lean's junk inverse makes $E_{k+1}$ the whole space.
-- source:
--   Grötschel, Lovász, Schrijver, The ellipsoid method and its consequences in combinatorial optimization, Combinatorica 1 (1981), p. 175, Lemma (2.2), (21)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_EllipsoidGLS_Rounded_Basic
import Definitions.Def_EllipsoidGLS_Rounded_Run

namespace EllipsoidGLS.Rounded

open Matrix

theorem lemma_2_2
    {n : ℕ} (hn : 2 ≤ n) (K : Set (Fin n → ℝ)) (a₀ c : Fin n → ℝ) (r R ε : ℝ)
    (hK : IsConvexBody K a₀ r R) (hc : 1 ≤ euclNorm c) (hε : 0 < ε) (hεr : ε < r)
    (hR : 1 ≤ R)
    (N : ℕ) (hN : N = itN n R r ε c)
    (x : ℕ → Fin n → ℝ) (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (feas : ℕ → Prop)
    (a d : ℕ → Fin n → ℝ)
    (hrun : IsRoundedRun K c a₀ R (itDelta n N R) (itP N) N x A feas a d) :
    ∀ k < N,
      MeasureTheory.volume (LinearOptimization.ellipsoid (x (k + 1)) (A (k + 1))) <
        ENNReal.ofReal (Real.exp (-1 / (5 * (n : ℝ)))) *
          MeasureTheory.volume (LinearOptimization.ellipsoid (x k) (A k)) := by sorry

end EllipsoidGLS.Rounded
