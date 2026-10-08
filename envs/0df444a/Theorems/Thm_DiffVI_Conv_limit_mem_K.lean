-- Prove2me | Theorems.Thm_DiffVI_Conv_limit_mem_K
-- name    : DiffVI.Conv.limit_mem_K
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:17.181136+00:00
-- url     : https://prove2.me/theorems/d4d99231-9905-4c56-b5df-5199d5a6a63b
-- title:
--   Proof of Theorem 7.1, p. 45 — a weak L²(0, T) limit of K-valued functions is K-valued almost everywhere
-- statement:
--   Let $K\subseteq\mathbb R^m$ be closed and convex and $T\in\mathbb R$. Let $g_1,g_2,\dots$ be functions in $L^2(0,T;\mathbb R^m)$ with $g_k(t)\in K$ for all $t\in(0,T]$, and suppose $g_k\rightharpoonup\hat u$ weakly in $L^2(0,T;\mathbb R^m)$. Then
--   $$\hat u(t)\in K\quad\text{for almost every }t\in[0,T].$$
--
--   In Theorem 7.1 this is applied to the piecewise constant interpolants $\hat u^{h_\nu}$, whose values are VI solutions and hence lie in $K$; it gives the constraint $\hat u(t)\in K$ of a weak solution.
--
--   **Formalization Note** Weak convergence in $L^2$ is tested against every $\psi\in L^2(0,T;\mathbb R^m)$, and the limit is required to lie in $L^2$.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 45, proof of Theorem 7.1 (Mazur's theorem: û(t) ∈ K for almost all t)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Conv_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace DiffVI.Conv

local notation "𝔼" k:max => EuclideanSpace ℝ (Fin k)

open SolodovSvaiterVI.Alg21

/-- Proof of Theorem 7.1, p. 45: a weak `L²(0, T)` limit of functions with values in a closed
convex set `K` takes values in `K` almost everywhere. -/
theorem limit_mem_K {m : ℕ} (K : Set (𝔼 m)) (hKcl : IsClosed K) (hKcv : Convex ℝ K) (T : ℝ)
    (g : ℕ → ℝ → 𝔼 m) (ul : ℝ → 𝔼 m)
    (hgK : ∀ k, ∀ t ∈ Set.Ioc (0 : ℝ) T, g k t ∈ K)
    (hgL2 : ∀ k, MemLp (g k) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hw : WeakL2Tendsto T g ul) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ul t ∈ K := by sorry

end DiffVI.Conv
