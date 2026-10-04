-- Prove2me | Theorems.Thm_BarvinokCount_ShortFormula_exists_index_reducing_vector
-- name    : BarvinokCount.ShortFormula.exists_index_reducing_vector
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:11:35.849053+00:00
-- url     : https://prove2.me/theorems/a002e832-8550-4803-8fb2-895805359efa
-- title:
--   Lemma 5.2 — a short nonzero lattice vector w in Lin{u} whose substitution lowers the index to (Ind K)^{(d−1)/d}
-- statement:
--   Let $k\ge1$ and let $u_1,\dots,u_k\in\mathbb{Z}^d$ be linearly independent; let $K=\operatorname{co}\{u_1,\dots,u_k\}$. Then there is a nonzero integral vector $w\in\operatorname{Lin}\{u_1,\dots,u_k\}\cap\mathbb{Z}^d$ such that
--
--   1. (a) the vectors $w,u_1,\dots,u_k$ belong to an open (linear) halfspace: there is $a\in\mathbb{R}^d$ with $\langle a,w\rangle>0$ and $\langle a,u_i\rangle>0$ for all $i$;
--   2. (b) for every $j$ such that $K_j=\operatorname{co}\{u_1,\dots,u_{j-1},w,u_{j+1},\dots,u_k\}$ is a $k$-dimensional cone (the generators $u_1,\dots,u_{j-1},w,u_{j+1},\dots,u_k$ are linearly independent),
--   $$\operatorname{Ind}K_j\le(\operatorname{Ind}K)^{(d-1)/d};$$
--   3. (c) $|w|\le|u_1|+\dots+|u_k|$, where $|\cdot|$ is the sup norm.
--
--   This is the key step of the decomposition: substituting $w$ for one generator at a time shrinks the index by a fixed power.
--
--   **Formalization Note** The paper's statement asserts a polynomial algorithm that constructs $w$; here the existence of $w$ with properties (a)–(c) is stated, which is the mathematical content of the algorithm's output. The hypothesis $k\ge1$ is added: for $k=0$ the span is $\{0\}$ and no nonzero $w$ exists. The halfspace in (a) is bounded by a hyperplane through the origin; an affine open halfspace would make (a) vacuous. The exponent $(d-1)/d$ is a real power.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), pp. 774–775, Lemma 5.2

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_coneIndex

namespace BarvinokCount.ShortFormula

theorem exists_index_reducing_vector {d k : ℕ} (hk : 1 ≤ k) (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) :
    ∃ w : Fin d → ℤ, w ≠ 0 ∧
      castVec w ∈ Submodule.span ℝ (Set.range fun i => castVec (u i)) ∧
      (∃ a : Fin d → ℝ, 0 < a ⬝ᵥ castVec w ∧ ∀ i, 0 < a ⬝ᵥ castVec (u i)) ∧
      (∀ j : Fin k, IsSimpleGens (Function.update u j w) →
        (coneIndex (Function.update u j w) : ℝ) ≤
          (coneIndex u : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ))) ∧
      supNorm w ≤ ∑ i, supNorm (u i) := by sorry

end BarvinokCount.ShortFormula
