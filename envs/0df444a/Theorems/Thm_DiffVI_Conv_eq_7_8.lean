-- Prove2me | Theorems.Thm_DiffVI_Conv_eq_7_8
-- name    : DiffVI.Conv.eq_7_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:40.292065+00:00
-- url     : https://prove2.me/theorems/4034ff4e-3f7e-4130-b825-7a0dff284dc0
-- title:
--   (7.8), proof of Theorem 7.1, pp. 45–47 — every limit pair satisfies x̂(t) − x̂(s) = ∫ₛᵗ [f(τ, x̂) + B(τ, x̂) û] dτ
-- statement:
--   Throughout, $K\subseteq\mathbb R^m$ is a nonempty closed convex set, $T>0$, $\Omega=[0,T]\times\mathbb R^n$, and $f:\Omega\to\mathbb R^n$, $B:\Omega\to\mathbb R^{n\times m}$, $G:\Omega\to\mathbb R^m$ satisfy the standing assumptions (A) (Lipschitz continuity on $\Omega$) and (B) (boundedness of $B$ on $\Omega$); $F:\mathbb R^m\to\mathbb R^m$.
--
--   Fix $\theta\in[0,1]$ and $x^0\in\mathbb R^n$. For every integer $N\ge \bar N$ (where $\bar N\ge 1$), let $h=T/N$ and let $x^{h,0}=x^0,x^{h,1},\dots,x^{h,N}$ and $u^{h,1},\dots,u^{h,N}$ be iterates of the time-stepping scheme (7.2). Assume the uniform bounds (7.5): there are positive constants $c_{0,x},c_{1,x},c_{0,u},c_{1,u}$ with
--   $$\|x^{h,i+1}\|\le c_{0,x}+c_{1,x}\|x^0\|,\qquad \|u^{h,i+1}\|\le c_{0,u}+c_{1,u}\|x^0\|$$
--   for all such $h$ and all $i=0,\dots,N-1$.
--
--   Let $N_1<N_2<\cdots$ be a strictly increasing sequence of integers $\ge\bar N$ (that is, step sizes $h_\nu=T/N_\nu\downarrow0$) along which the piecewise linear interpolants $\hat x^{h_\nu}$ converge uniformly on $[0,T]$ to $\hat x$ and the piecewise constant interpolants $\hat u^{h_\nu}$ converge weakly in $L^2(0,T;\mathbb R^m)$ to $\hat u$.
--
--   Then $\tau\mapsto f(\tau,\hat x(\tau))+B(\tau,\hat x(\tau))\hat u(\tau)$ is integrable on $[0,T]$ and, for all $0\le s\le t\le T$,
--   $$\hat x(t)-\hat x(s)=\int_s^t\big[f(\tau,\hat x(\tau))+B(\tau,\hat x(\tau))\hat u(\tau)\big]\,d\tau.\qquad(7.8)$$
--
--   This is the differential-equation part of the weak-solution property of the limit; it holds without condition (a) or (b) on $F$.
--
--   **Formalization Note** Step sizes are $h=T/N$ with $N=N_h+1\ge1$ an integer, so that the grid $t_{h,i}=ih$ ends exactly at $T$; "$h\in(0,\bar h]$" becomes "$N\ge\bar N$" and "$h_\nu\downarrow0$" a strictly increasing sequence of $N$'s.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, pp. 45–47, (7.8), proof of Theorem 7.1

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Conv_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace DiffVI.Conv

local notation "𝔼" k:max => EuclideanSpace ℝ (Fin k)

open SolodovSvaiterVI.Alg21

/-- (7.8), proof of Theorem 7.1, pp. 45–47: every limit pair satisfies the integral equation
`x̂(t) - x̂(s) = ∫ₛᵗ [f(τ, x̂(τ)) + B(τ, x̂(τ)) û(τ)] dτ`. -/
theorem eq_7_8 {n m : ℕ} (K : Set (𝔼 m)) (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K)
    (T : ℝ) (hT : 0 < T) (f : ℝ → 𝔼 n → 𝔼 n) (B : ℝ → 𝔼 n → (𝔼 m →L[ℝ] 𝔼 n))
    (G : ℝ → 𝔼 n → 𝔼 m) (hA : DiffVI.Exist.CondA T f B G) (hB : DiffVI.Exist.CondB T B) (F : 𝔼 m → 𝔼 m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (x0 : 𝔼 n) (xs : ℕ → ℕ → 𝔼 n) (us : ℕ → ℕ → 𝔼 m)
    (Nbar : ℕ) (hNbar : 1 ≤ Nbar)
    (hsch : ∀ N ≥ Nbar, IsScheme K f B G F T θ x0 N (xs N) (us N))
    (h75 : ∃ c0x c1x c0u c1u : ℝ, 0 < c0x ∧ 0 < c1x ∧ 0 < c0u ∧ 0 < c1u ∧
      ∀ N ≥ Nbar, ∀ i < N, ‖xs N (i + 1)‖ ≤ c0x + c1x * ‖x0‖ ∧
        ‖us N (i + 1)‖ ≤ c0u + c1u * ‖x0‖)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (hφN : ∀ k, Nbar ≤ φ k) (xl : ℝ → 𝔼 n) (ul : ℝ → 𝔼 m)
    (hxl : TendstoUniformlyOn (fun k => xhat T (φ k) (xs (φ k))) xl atTop (Set.Icc (0 : ℝ) T))
    (hul : WeakL2Tendsto T (fun k => uhat T (φ k) (us (φ k))) ul) :
    IntegrableOn (fun τ => f τ (xl τ) + B τ (xl τ) (ul τ)) (Set.Icc (0 : ℝ) T) ∧
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      xl t - xl s = ∫ τ in s..t, (f τ (xl τ) + B τ (xl τ) (ul τ)) := by sorry

end DiffVI.Conv
