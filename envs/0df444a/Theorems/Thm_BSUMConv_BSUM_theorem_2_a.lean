-- Prove2me | Theorems.Thm_BSUMConv_BSUM_theorem_2_a
-- name    : BSUMConv.BSUM.theorem_2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:44.954804+00:00
-- url     : https://prove2.me/theorems/8a376d36-364e-4f73-bf30-a8752f622ad0
-- title:
--   Theorem 2(a), p. 10 — limit points of cyclic BSUM with quasi-convex u_i and unique block minimisers are coordinatewise stationary, and stationary where f is regular
-- statement:
--   Consider problem (12), $\min f(x)$ over $x\in\mathcal X=\mathcal X_1\times\cdots\times\mathcal X_n$, where each $\mathcal X_i\subseteq\mathbb R^{m_i}$ is closed and convex and $f$ is continuous on $\mathcal X$. Let the approximation functions $u_i(x_i,y)$ satisfy Assumption 2:
--
--   1. (B1) $u_i(y_i,y)=f(y)$ for $y\in\mathcal X$;
--   2. (B2) $u_i(x_i,y)\ge f(y_1,\dots,y_{i-1},x_i,y_{i+1},\dots,y_n)$ for $x_i\in\mathcal X_i$, $y\in\mathcal X$;
--   3. (B3) $u_i'(x_i,y;d_i)\big|_{x_i=y_i}=f'(y;d)$ for $y\in\mathcal X$ and $d=(0,\dots,d_i,\dots,0)$ with $y_i+d_i\in\mathcal X_i$;
--   4. (B4) $u_i$ is continuous in $(x_i,y)$.
--
--   Suppose moreover that each $u_i(x_i,y)$ is quasi-convex in $x_i$ and that the subproblem $\min_{x_i\in\mathcal X_i}u_i(x_i,y)$ has a unique solution for every $y\in\mathcal X$ and every block $i$. Let $(x^r)$ be the iterates of the BSUM algorithm with the cyclic rule, starting from $x^0\in\mathcal X$. Then every limit point $z$ of $(x^r)$ satisfies $z\in\mathcal X$ and
--
--   $$f'(z;d)\ \ge\ 0\qquad\forall\,d=(0,\dots,d_k,\dots,0)\ \text{with}\ z_k+d_k\in\mathcal X_k,\quad k=1,\dots,n,$$
--
--   that is, $z$ is coordinatewise stationary. In addition, if $f$ is regular at $z$, then $z$ is a stationary point of (12).
--
--   The theorem extends the classical convergence result for cyclic block coordinate descent to methods that minimise a locally tight upper bound of $f$ in one block at a time, covering for example EM- and DC-type algorithms.
--
--   **Formalization Note** The paper says "coordinatewise minimum" (defined on p. 4 by $f(z+(0,\dots,d_k,\dots,0))\ge f(z)$), but its proof ends with the coordinatewise stationarity displayed above and calls that "coordinatewise minimum". The literal minimum claim is false: with one block, $\mathcal X=[-1,1]$, $f(x)=-x^2$, $u(x,y)=-y^2-2y(x-y)+(x-y)^2$ all hypotheses hold, the iterates from $x^0=0$ stay at $0$, and $f(1)<f(0)$. The statement therefore asserts coordinatewise stationarity. Stationarity and regularity refer to $f$ extended by $+\infty$ off $\mathcal X$. The cyclic rule updates block $r \bmod n$ (0-based) on the step $x^r\to x^{r+1}$, a relabelling of Fig. 2's $i=(r\bmod n)+1$.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 10, Theorem 2(a); proof pp. 10–12

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSUM_Setting

namespace BSUMConv.BSUM

open TsengBCD.Stationary Filter Topology

/-- Theorem 2(a), p. 10: if each `u_i(x_i, y)` is quasi-convex in `x_i`, Assumption 2 holds and the
subproblem (13) has a unique solution at every point of `X`, then every limit point `z` of the
cyclic BSUM iterates is coordinatewise stationary for (12) (the paper: "coordinatewise
minimum"), and `z` is a stationary point of (12) if `f` is regular at `z`. -/
theorem theorem_2_a {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (hXconv : ∀ i, Convex ℝ (Xs i)) (hXclosed : ∀ i, IsClosed (Xs i))
    (f : X n → ℝ) (hf : ContinuousOn f (Xset Xs))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (hA2 : Assumption2 Xs f u)
    (hqc : BlockQuasiconvex Xs u) (huniq : ∀ i, UniqueBlockMin Xs u i)
    (s : ℕ → Fin N) (hs : IsCyclic s) (x : ℕ → X n) (hx : IsBSUMRun Xs u s x)
    (z : X n) (hz : MapClusterPt z atTop x) :
    IsCoordStationary Xs f z ∧
      (IsRegularAt (fext f (Xset Xs)) z → IsStationary (fext f (Xset Xs)) z) := by sorry

end BSUMConv.BSUM
