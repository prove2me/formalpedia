-- Prove2me | Theorems.Thm_EllipsoidGLS_Rounded_lemma_2_1
-- name    : EllipsoidGLS.Rounded.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:23:16.672327+00:00
-- url     : https://prove2.me/theorems/27cc44e0-d999-45c1-9258-8f06e4f3f485
-- title:
--   Lemma (2.1), p. 174 — A₀, …, A_N are positive definite, ‖x_k‖ ≤ ‖a₀‖ + R2^k, ‖A_k‖ ≤ R²2^k, ‖A_k⁻¹‖ ≤ R⁻²4^k
-- statement:
--   Let $n\ge 2$ and let $(K,a_0,r,R)$ be a compact convex body in $\mathbb{R}^n$, $S(a_0,r)\subseteq K\subseteq S(a_0,R)$. Let $c\in\mathbb{R}^n$ and $\varepsilon>0$ satisfy the paper's standing assumptions $\varepsilon<r$ and $\|c\|\ge 1$, and assume $R\ge 1$. Let
--   $$N = 4n^2\left\lceil \log\frac{2R^2\|c\|}{r\varepsilon}\right\rceil,\qquad \delta=\frac{R^2 4^{-N}}{300n},\qquad p=5N,$$
--   and let $(x_k,A_k)$ be any run of the rounded ellipsoid method for $N$ steps with oracle precision $\delta$ and rounding precision $p$. Then for every $k=0,1,\dots,N$ the matrix $A_k$ is positive definite and
--   $$\|x_k\|\le\|a_0\|+R\,2^k,\qquad \|A_k\|\le R^2 2^k,\qquad \|A_k^{-1}\|\le R^{-2}4^k .$$
--
--   The lemma keeps the iteration well defined (every $A_k$ is invertible and $\sqrt{a^{\mathsf T}A_ka}>0$) and bounds the size of all numbers that occur, which the paper uses for the polynomial running time.
--
--   **Formalization Note** Norms are Euclidean, and the matrix norm is the spectral norm. For the symmetric positive definite $A_k$ the two matrix bounds are stated as quadratic-form bounds: $v^{\mathsf T}A_kv\le R^2 2^k\,v^{\mathsf T}v$ for all $v$ (largest eigenvalue at most $R^22^k$) and $R^2 4^{-k}\,v^{\mathsf T}v\le v^{\mathsf T}A_kv$ for all $v$ (smallest eigenvalue at least $R^24^{-k}$, i.e. $\|A_k^{-1}\|\le R^{-2}4^k$). The hypothesis $R\ge 1$ is not on the page: the iteration's $N$ and rounding precision $2^{-p}$ are absolute numbers, and for $R=r=2^{-1000}$, $\varepsilon=r/2$, $n=2$ (so $N=32$, $p=160$) the rounding may turn $A_1$ into the zero matrix, which refutes the lemma; $R\ge 1$ makes the rounding error $n2^{-5N}$ negligible against $R^24^{-N}$. The hypotheses $\varepsilon<r$ and $\|c\|\ge 1$ are the paper's "without loss of generality" assumptions (p. 173); they make the logarithm exceed $\log 2$, so $N\ge 4n^2$.
-- source:
--   Grötschel, Lovász, Schrijver, The ellipsoid method and its consequences in combinatorial optimization, Combinatorica 1 (1981), p. 174, Lemma (2.1), (12)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_EllipsoidGLS_Rounded_Basic
import Definitions.Def_EllipsoidGLS_Rounded_Run

namespace EllipsoidGLS.Rounded

open Matrix

theorem lemma_2_1
    {n : ℕ} (hn : 2 ≤ n) (K : Set (Fin n → ℝ)) (a₀ c : Fin n → ℝ) (r R ε : ℝ)
    (hK : IsConvexBody K a₀ r R) (hc : 1 ≤ euclNorm c) (hε : 0 < ε) (hεr : ε < r)
    (hR : 1 ≤ R)
    (N : ℕ) (hN : N = itN n R r ε c)
    (x : ℕ → Fin n → ℝ) (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (feas : ℕ → Prop)
    (a d : ℕ → Fin n → ℝ)
    (hrun : IsRoundedRun K c a₀ R (itDelta n N R) (itP N) N x A feas a d) :
    ∀ k ≤ N, (A k).PosDef ∧
      euclNorm (x k) ≤ euclNorm a₀ + R * 2 ^ k ∧
      (∀ v : Fin n → ℝ, v ⬝ᵥ (A k).mulVec v ≤ R ^ 2 * 2 ^ k * (v ⬝ᵥ v)) ∧
      (∀ v : Fin n → ℝ, R ^ 2 * (4 : ℝ) ^ (-(k : ℤ)) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A k).mulVec v) := by sorry

end EllipsoidGLS.Rounded
