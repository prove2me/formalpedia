-- Prove2me | Theorems.Thm_EllipsoidGLS_Rounded_lemma_2_3
-- name    : EllipsoidGLS.Rounded.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:23:29.03682+00:00
-- url     : https://prove2.me/theorems/67d867d8-43f7-4a3d-b27b-504aadc40f15
-- title:
--   Lemma (2.3), p. 175 — E_k ⊇ K_k for k = 0, 1, …, N
-- statement:
--   Let $n\ge 2$, let $(K,a_0,r,R)$ be a compact convex body in $\mathbb{R}^n$, let $c\in\mathbb{R}^n$ and $\varepsilon>0$ satisfy $\varepsilon<r$ and $\|c\|\ge1$, and assume $R\ge1$ and $\varepsilon\le1$. Let $(x_k,A_k)$ be any run of the rounded ellipsoid method for
--   $$N = 4n^2\left\lceil \log\frac{2R^2\|c\|}{r\varepsilon}\right\rceil$$
--   steps with $\delta=R^24^{-N}/(300n)$ and $p=5N$, and put
--   $$\zeta_k=\max\{c^{\mathsf T}x_j : 0\le j<k,\ j\text{ feasible}\},\qquad K_k = K\cap\{x : c^{\mathsf T}x\ge\zeta_k\}$$
--   ($K_k=K$ when no $j<k$ is feasible). Then for $k=0,1,\dots,N$
--   $$K_k\subseteq E_k=\{x : (x-x_k)^{\mathsf T}A_k^{-1}(x-x_k)\le 1\}.$$
--
--   The ellipsoids therefore never lose a point of the body that is at least as good as the best feasible centre found so far; combined with the volume decrease, this is the heart of the correctness proof.
--
--   **Formalization Note** $K_k$ is encoded as $\{y\in K : c^{\mathsf T}y\ge c^{\mathsf T}x_j$ for every feasible $j<k\}$, never with a real supremum (which would be $0$ on the empty set). $A_k$ is positive definite by Lemma (2.1), so $E_k$ is a genuine ellipsoid; positive definiteness is a consequence, not a hypothesis. Two hypotheses are added to the page. $R\ge1$: see Lemma (2.1). $\varepsilon\le1$: for $R=r=10^{13}$, $\varepsilon=0.99r$, $n=2$ one gets $N=16$ and $\delta\approx3.9\cdot10^{13}>2r$, and a valid weak oracle may then declare every centre infeasible with $d=c$ and so cut away all of $K$, refuting the lemma; with $\varepsilon<r\le R$ and $\varepsilon\le1$ one has $N\ge16\log(2R)$, hence $R\le2^N$ and $\delta<r$, which the paper's estimate (30) uses.
-- source:
--   Grötschel, Lovász, Schrijver, The ellipsoid method and its consequences in combinatorial optimization, Combinatorica 1 (1981), p. 175, Lemma (2.3), (22)–(23)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_EllipsoidGLS_Rounded_Basic
import Definitions.Def_EllipsoidGLS_Rounded_Run

namespace EllipsoidGLS.Rounded

open Matrix

theorem lemma_2_3
    {n : ℕ} (hn : 2 ≤ n) (K : Set (Fin n → ℝ)) (a₀ c : Fin n → ℝ) (r R ε : ℝ)
    (hK : IsConvexBody K a₀ r R) (hc : 1 ≤ euclNorm c) (hε : 0 < ε) (hεr : ε < r)
    (hR : 1 ≤ R)
    (hε1 : ε ≤ 1)
    (N : ℕ) (hN : N = itN n R r ε c)
    (x : ℕ → Fin n → ℝ) (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (feas : ℕ → Prop)
    (a d : ℕ → Fin n → ℝ)
    (hrun : IsRoundedRun K c a₀ R (itDelta n N R) (itP N) N x A feas a d) :
    ∀ k ≤ N, Kk K c x feas k ⊆ LinearOptimization.ellipsoid (x k) (A k) := by sorry

end EllipsoidGLS.Rounded
