-- Prove2me | Theorems.Thm_BarvinokCount_ShortFormula_cone_lattice_exp_sum_hasSum
-- name    : BarvinokCount.ShortFormula.cone_lattice_exp_sum_hasSum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:28:31.500395+00:00
-- url     : https://prove2.me/theorems/3c644800-0bdc-41a0-be7b-c174a9134220
-- title:
--   Proposition 2.4 with Remark 2.5 — the exponential sum over a simple rational cone has the closed form σ(K; c)
-- statement:
--   Let $u_1,\dots,u_k\in\mathbb{Z}^d$ be linearly independent and $K=\operatorname{co}\{u_1,\dots,u_k\}$ the simple rational cone they generate. Let $c\in\mathbb{R}^d$ be such that the linear function $\langle c,\cdot\rangle$ decreases along the extreme rays of $K$, i.e. $\langle c,u_i\rangle<0$ for all $i$. Then the series over the integral points of $K$ converges (absolutely) and
--   $$\sum_{x\in K\cap\mathbb{Z}^d}\exp\{\langle c,x\rangle\}=\Bigl(\sum_{x\in\Pi\cap\mathbb{Z}^d}\exp\{\langle c,x\rangle\}\Bigr)\cdot\prod_{i=1}^k\frac{1}{1-\exp\{\langle c,u_i\rangle\}}=\sigma(K;c),$$
--   where $\Pi=\{\sum_i\alpha_iu_i:0\le\alpha_i<1\}$ is the semi-open parallelepiped of the generators.
--
--   This links the closed form of $\sigma$, used throughout the mission, to the exponential sum it represents; it is the starting point of every identity between the functions $\sigma$.
--
--   **Formalization Note** The statement is an unconditional (`HasSum`) summation over the integral points of $K$. The meromorphic continuation to $c\in\mathbb{C}^d$ and the description of the real singular points are not stated: $\sigma$ is defined by the closed form, and regularity is defined as $\langle c,u_i\rangle\ne0$ for all $i$, which is what the proposition's last sentence asserts.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), pp. 770–771, Proposition 2.4 and Remark 2.5

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_sigma

namespace BarvinokCount.ShortFormula

theorem cone_lattice_exp_sum_hasSum {d k : ℕ} (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u)
    (c : Fin d → ℝ) (hc : ∀ i, c ⬝ᵥ castVec (u i) < 0) :
    HasSum (fun z : {z : Fin d → ℤ // castVec z ∈ cone u} => Real.exp (c ⬝ᵥ castVec z.1))
      (sigma u c) := by sorry

end BarvinokCount.ShortFormula
