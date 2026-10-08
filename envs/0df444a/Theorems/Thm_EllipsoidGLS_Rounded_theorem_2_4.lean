-- Prove2me | Theorems.Thm_EllipsoidGLS_Rounded_theorem_2_4
-- name    : EllipsoidGLS.Rounded.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:24:01.721654+00:00
-- url     : https://prove2.me/theorems/c09673f8-f147-4bf2-a2e5-c6eae6bfb320
-- title:
--   Theorem (2.4), p. 176 — the best feasible centre of the rounded ellipsoid method is ε-optimal
-- statement:
--   Let $n\ge 2$ and let $(K,a_0,r,R)$ be a compact convex body in $\mathbb{R}^n$: $K$ is compact and convex, $0<r\le R$, and $S(a_0,r)\subseteq K\subseteq S(a_0,R)$ for the Euclidean balls $S(a_0,\rho)$. Let $c\in\mathbb{R}^n$ be the objective and $\varepsilon>0$ the accuracy, with the paper's standing assumptions $\varepsilon<r$ and $\|c\|\ge 1$, and assume $R\ge 1$ and $\varepsilon\le 1$. Let
--   $$N = 4n^2\left\lceil \log\frac{2R^2\|c\|}{r\varepsilon}\right\rceil,\qquad \delta=\frac{R^24^{-N}}{300n},\qquad p=5N,$$
--   and let $x_0,x_1,\dots$ be the centres of any run of the rounded ellipsoid method with a weak separation oracle of precision $\delta$ and rounding to precision $2^{-p}$. If $j<N$ is a feasible index with
--   $$c^{\mathsf T}x_j=\max\{c^{\mathsf T}x_k : 0\le k<N,\ k\text{ feasible}\},$$
--   then
--   $$c^{\mathsf T}x_j\ge\max\{c^{\mathsf T}x : x\in K\}-\varepsilon .$$
--
--   Since a feasible centre lies within $\delta$ of $K$, this says that the rounded ellipsoid method solves the weak optimization problem for $K$ with a number of oracle calls and a numerical precision that are polynomial in $n$, $\log R$, $\log(1/r)$, $\log\|c\|$ and $\log(1/\varepsilon)$. It is the main theorem of Section 2 and the basis of the paper's equivalence of weak separation and weak optimization.
--
--   **Formalization Note** The conclusion "$\ge\max-\varepsilon$" is stated as $c^{\mathsf T}y-\varepsilon\le c^{\mathsf T}x_j$ for every $y\in K$, which is equivalent because $K$ is compact and nonempty. The theorem holds for every run: every sequence of valid oracle answers and every symmetric rounding within $2^{-p}$ entrywise (see the definition of runs). Norms are Euclidean (`euclNorm`), not Lean's sup norm. Positive definiteness of the matrices $A_k$ is a consequence (Lemma (2.1)), not a hypothesis. Two hypotheses are added to the page, because the page's $N$, $\delta$ and $p$ are absolute numbers and the theorem fails at extreme scales: $R\ge1$ (for $R=r=2^{-1000}$, $\varepsilon=r/2$, $n=2$ the rounding can collapse $A_1$ to $0$ and every centre can round back to $a_0$) and $\varepsilon\le1$ (for $R=r=10^{13}$, $\varepsilon=0.99r$, $n=2$ one gets $\delta>2r$, and a valid oracle can declare every centre but the last infeasible). The polynomial running time and the rationality of the data are not part of the statement.
-- source:
--   Grötschel, Lovász, Schrijver, The ellipsoid method and its consequences in combinatorial optimization, Combinatorica 1 (1981), p. 176, Theorem (2.4), (31)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_EllipsoidGLS_Rounded_Basic
import Definitions.Def_EllipsoidGLS_Rounded_Run

namespace EllipsoidGLS.Rounded

open Matrix

theorem theorem_2_4
    {n : ℕ} (hn : 2 ≤ n) (K : Set (Fin n → ℝ)) (a₀ c : Fin n → ℝ) (r R ε : ℝ)
    (hK : IsConvexBody K a₀ r R) (hc : 1 ≤ euclNorm c) (hε : 0 < ε) (hεr : ε < r)
    (hR : 1 ≤ R)
    (hε1 : ε ≤ 1)
    (N : ℕ) (hN : N = itN n R r ε c)
    (x : ℕ → Fin n → ℝ) (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (feas : ℕ → Prop)
    (a d : ℕ → Fin n → ℝ)
    (hrun : IsRoundedRun K c a₀ R (itDelta n N R) (itP N) N x A feas a d)
    (j : ℕ) (hj : j < N) (hfj : feas j)
    (hmax : ∀ k < N, feas k → c ⬝ᵥ x k ≤ c ⬝ᵥ x j) :
    ∀ y ∈ K, c ⬝ᵥ y - ε ≤ c ⬝ᵥ x j := by sorry

end EllipsoidGLS.Rounded
