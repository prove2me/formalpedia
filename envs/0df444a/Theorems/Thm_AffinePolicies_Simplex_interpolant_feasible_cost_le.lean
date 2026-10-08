-- Prove2me | Theorems.Thm_AffinePolicies_Simplex_interpolant_feasible_cost_le
-- name    : AffinePolicies.Simplex.interpolant_feasible_cost_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:38:22.650792+00:00
-- url     : https://prove2.me/theorems/5149cacd-17c3-4922-8b33-5a0a391a3926
-- title:
--   Theorem 1, proof, (3)–(5), PDF p. 7 — the affine interpolant of a feasible solution is feasible and no more costly
-- statement:
--   Let $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}$, $d\in\mathbb R^{n_2}$, let $b^1,\dots,b^{m+1}\in\mathbb R^m$ be affinely independent and $\mathcal U=\operatorname{conv}(b^1,\dots,b^{m+1})$. Let $(x^*,y^*)$ be any feasible two-stage solution of $\Pi_{Adapt}(\mathcal U)$, and let
--   $$\tilde y(b)=YQ^{-1}\big(b-b^{m+1}\big)+y^*(b^{m+1})$$
--   be the affine interpolant of the vertex decisions $y^*(b^1),\dots,y^*(b^{m+1})$. Then
--
--   1. $(x^*,\tilde y)$ is feasible for $\Pi_{Adapt}(\mathcal U)$: $\tilde y(b)\ge 0$ and $Ax^*+B\tilde y(b)\ge b$ for every $b\in\mathcal U$;
--   2. every bound on the worst-case cost of $(x^*,y^*)$ is a bound for $(x^*,\tilde y)$:
--   $$c^Tx^*+\max_{b\in\mathcal U}d^T\tilde y(b)\ \le\ c^Tx^*+\max_{j=1,\dots,m+1}d^Ty^*(b^j)\ \le\ c^Tx^*+\sup_{b\in\mathcal U}d^Ty^*(b).$$
--
--   Applied to an optimal $(x^*,y^*)$, this gives (5): the affine solution costs at most $z_{Adapt}(\mathcal U)$.
--
--   **Formalization Note** The paper applies this to an optimal solution; it is stated here for every feasible solution, which needs no optimum and is stronger. The cost comparison is stated through worst-case bounds: for every $t$, if $c^Tx^*+d^Ty^*(b)\le t$ on $\mathcal U$ then $c^Tx^*+d^T\tilde y(b)\le t$ on $\mathcal U$. No sign conditions on $c$, $d$ or the vertices are needed.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 1, proof, (3)–(5), PDF p. 7

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

namespace AffinePolicies.Simplex

theorem interpolant_feasible_cost_le {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ)
    (v : Fin (m + 1) → Fin m → ℝ) (hv : AffineIndependent ℝ v)
    (xs : Fin n₁ → ℝ) (ys : (Fin m → ℝ) → Fin n₂ → ℝ)
    (hfs : Feasible A B (simplexSet v) xs ys) :
    Feasible A B (simplexSet v) xs (interpolant v ys) ∧
      ∀ t : ℝ, CostLE c d (simplexSet v) xs ys t →
        CostLE c d (simplexSet v) xs (interpolant v ys) t := by sorry

end AffinePolicies.Simplex
