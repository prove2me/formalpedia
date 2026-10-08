-- Prove2me | Theorems.Thm_DiffVI_Conv_eq_7_9
-- name    : DiffVI.Conv.eq_7_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:24.90811+00:00
-- url     : https://prove2.me/theorems/55c5febc-30ec-43ff-8bc6-3ff7d2bb2661
-- title:
--   (7.9), proof of Theorem 7.1, p. 48 — liminf ∫₀ᵀ ûᵀDû along a weakly convergent sequence ≥ ∫₀ᵀ ûᵀDû for psd D
-- statement:
--   Let $D\in\mathbb R^{m\times m}$ be positive semidefinite ($u^{\mathsf T}Du\ge0$ for all $u$, $D$ not necessarily symmetric), let $T\in\mathbb R$, and let $g_1,g_2,\dots\in L^2(0,T;\mathbb R^m)$ converge weakly in $L^2(0,T;\mathbb R^m)$ to $\hat u$. Then
--   $$\liminf_{k\to\infty}\int_0^T g_k(t)^{\mathsf T}Dg_k(t)\,dt\;\ge\;\int_0^T\hat u(t)^{\mathsf T}D\hat u(t)\,dt.\qquad(7.9)$$
--
--   In Theorem 7.1 this is applied to $g_k=\hat u^{h_\nu}$ and gives the variational inequality for the limit under condition (b), $F(u)=Du$.
--
--   **Formalization Note** The liminf is stated in $\varepsilon$-form: for every $\varepsilon>0$, eventually $\int_0^T g_k^{\mathsf T}Dg_k\,dt\ge\int_0^T\hat u^{\mathsf T}D\hat u\,dt-\varepsilon$. This avoids Lean's convention for a real liminf of a sequence not bounded below.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 48, (7.9), proof of Theorem 7.1, case (b)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Conv_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace DiffVI.Conv

local notation "𝔼" k:max => EuclideanSpace ℝ (Fin k)

open SolodovSvaiterVI.Alg21

/-- (7.9), proof of Theorem 7.1, p. 48: for a positive semidefinite `D`, the quadratic functional
`u ↦ ∫₀ᵀ uᵀ D u` is weakly sequentially lower semicontinuous on `L²(0, T)`
(liminf stated in ε-form). -/
theorem eq_7_9 {m : ℕ} (D : 𝔼 m →L[ℝ] 𝔼 m) (hD : DiffVI.Exist.IsPSD D) (T : ℝ)
    (g : ℕ → ℝ → 𝔼 m) (ul : ℝ → 𝔼 m)
    (hgL2 : ∀ k, MemLp (g k) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hw : WeakL2Tendsto T g ul) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ t in Set.Icc (0 : ℝ) T, ⟪ul t, D (ul t)⟫_ℝ) - ε ≤
        ∫ t in Set.Icc (0 : ℝ) T, ⟪g k t, D (g k t)⟫_ℝ := by sorry

end DiffVI.Conv
