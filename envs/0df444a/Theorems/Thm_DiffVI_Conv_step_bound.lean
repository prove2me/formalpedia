-- Prove2me | Theorems.Thm_DiffVI_Conv_step_bound
-- name    : DiffVI.Conv.step_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:21.469051+00:00
-- url     : https://prove2.me/theorems/f21195c7-7ca4-4bbd-a164-6d3e311b70e2
-- title:
--   Proof of Theorem 7.1, p. 44 — ‖x^{h,i+1} − x^{h,i}‖ ≤ L h, so the interpolants x̂^h are Lipschitz uniformly in h
-- statement:
--   Throughout, $K\subseteq\mathbb R^m$ is a nonempty closed convex set, $T>0$, $\Omega=[0,T]\times\mathbb R^n$, and $f:\Omega\to\mathbb R^n$, $B:\Omega\to\mathbb R^{n\times m}$, $G:\Omega\to\mathbb R^m$ satisfy the standing assumptions (A) (Lipschitz continuity on $\Omega$) and (B) (boundedness of $B$ on $\Omega$); $F:\mathbb R^m\to\mathbb R^m$.
--
--   Fix $\theta\in[0,1]$ and $x^0\in\mathbb R^n$. For every integer $N\ge \bar N$ (where $\bar N\ge 1$), let $h=T/N$ and let $x^{h,0}=x^0,x^{h,1},\dots,x^{h,N}$ and $u^{h,1},\dots,u^{h,N}$ be iterates of the time-stepping scheme (7.2). Assume the uniform bounds (7.5): there are positive constants $c_{0,x},c_{1,x},c_{0,u},c_{1,u}$ with
--   $$\|x^{h,i+1}\|\le c_{0,x}+c_{1,x}\|x^0\|,\qquad \|u^{h,i+1}\|\le c_{0,u}+c_{1,u}\|x^0\|$$
--   for all such $h$ and all $i=0,\dots,N-1$.
--
--   Then there is a constant $L>0$, independent of $h$ (it may depend on $\|x^0\|$), such that for all sufficiently small $h=T/N$ (with $N\ge\bar N$) and all $i=0,\dots,N-1$,
--   $$\|x^{h,i+1}-x^{h,i}\|\le L\,h,$$
--   and the interpolant $\hat x^h$ is $L$-Lipschitz on $[0,T]$: $\|\hat x^h(t)-\hat x^h(s)\|\le L|t-s|$ for $s,t\in[0,T]$.
--
--   This equicontinuity is what allows the Arzelà–Ascoli theorem to extract a uniformly convergent subsequence of $\{\hat x^h\}$ in Theorem 7.1.
--
--   **Formalization Note** Step sizes are $h=T/N$ with $N=N_h+1\ge1$ an integer, so that the grid $t_{h,i}=ih$ ends exactly at $T$; "$h\in(0,\bar h]$" becomes "$N\ge\bar N$" and "$h_\nu\downarrow0$" a strictly increasing sequence of $N$'s.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 44, proof of Theorem 7.1 (step bound ‖x^{h,i+1} − x^{h,i}‖ ≤ L_{x⁰} h)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Conv_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace DiffVI.Conv

local notation "𝔼" k:max => EuclideanSpace ℝ (Fin k)

open SolodovSvaiterVI.Alg21

/-- Proof of Theorem 7.1, p. 44: under (7.5), `‖x^{h,i+1} - x^{h,i}‖ ≤ L h` for all small `h`,
so the interpolants `x̂^h` are Lipschitz on `[0, T]` with a constant independent of `h`. -/
theorem step_bound {n m : ℕ} (K : Set (𝔼 m)) (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K)
    (T : ℝ) (hT : 0 < T) (f : ℝ → 𝔼 n → 𝔼 n) (B : ℝ → 𝔼 n → (𝔼 m →L[ℝ] 𝔼 n))
    (G : ℝ → 𝔼 n → 𝔼 m) (hA : DiffVI.Exist.CondA T f B G) (hB : DiffVI.Exist.CondB T B) (F : 𝔼 m → 𝔼 m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (x0 : 𝔼 n) (xs : ℕ → ℕ → 𝔼 n) (us : ℕ → ℕ → 𝔼 m)
    (Nbar : ℕ) (hNbar : 1 ≤ Nbar)
    (hsch : ∀ N ≥ Nbar, IsScheme K f B G F T θ x0 N (xs N) (us N))
    (h75 : ∃ c0x c1x c0u c1u : ℝ, 0 < c0x ∧ 0 < c1x ∧ 0 < c0u ∧ 0 < c1u ∧
      ∀ N ≥ Nbar, ∀ i < N, ‖xs N (i + 1)‖ ≤ c0x + c1x * ‖x0‖ ∧
        ‖us N (i + 1)‖ ≤ c0u + c1u * ‖x0‖) :
    ∃ L : ℝ, 0 < L ∧ ∃ N1 : ℕ, ∀ N ≥ max Nbar N1,
      (∀ i < N, ‖xs N (i + 1) - xs N i‖ ≤ L * (T / N)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖xhat T N (xs N) t - xhat T N (xs N) s‖ ≤ L * |t - s|) := by sorry

end DiffVI.Conv
