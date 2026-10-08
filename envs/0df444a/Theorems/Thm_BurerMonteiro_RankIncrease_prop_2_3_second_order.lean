-- Prove2me | Theorems.Thm_BurerMonteiro_RankIncrease_prop_2_3_second_order
-- name    : BurerMonteiro.RankIncrease.prop_2_3_second_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:39:19.050486+00:00
-- url     : https://prove2.me/theorems/836c4945-bca1-4a07-bb8f-8d8e1f94b94a
-- title:
--   Proposition 2.3 (second-order part): $S^*\bullet(DD^T)\ge 0$ on the tangent directions (12)
-- statement:
--   Let $C, A_1,\dots,A_m\in\mathcal S^n$ be symmetric and $b\in\mathbb R^m$, under the standing assumptions of §2.1, and let $r$ be a positive integer with $r\le n$. Let $R^*\in\mathbb R^{n\times r}$ be a regular local minimum of $(N_r)$, and let $y^*\in\mathbb R^m$ be its Lagrange multiplier, i.e. $S^*=C-\sum_i y^*_iA_i$ satisfies $S^*R^*=0$. Then
--   $$S^*\bullet(DD^{T})\ge 0\tag{11}$$
--   for every $D\in\mathbb R^{n\times r}$ satisfying
--   $$A_iR^*\bullet D=0\quad\forall\, i=1,\dots,m.\tag{12}$$
--
--   This is the second-order necessary condition for $(N_r)$: the Hessian of the Lagrangian, $2S^*\bullet(DD^T)$ by (9), is nonnegative on the tangent space of the constraints. Applied at $\hat R$ in the direction of the appended column it yields $S^*\succeq0$ in the proof of Proposition 2.5.
--
--   **Formalization Note** The statement quantifies over every $y$ with $S(y)R^*=0$; by the uniqueness part of Proposition 2.3 this is exactly the multiplier $y^*$. Condition (12) is $\operatorname{trace}((A_iR^*)^TD)=0$ for all $i$.
-- source:
--   Burer & Monteiro, A nonlinear programming algorithm for solving semidefinite programs via low-rank factorization (manuscript of March 9, 2001; Math. Program. 95 (2003)), p. 6, Proposition 2.3, Eqs. (11)–(12)

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

open Matrix
open scoped Matrix.Norms.Frobenius

namespace BurerMonteiro.RankIncrease

/-- Proposition 2.3, second-order part (p. 6): if `R∗` is a local minimum of `(N_r)` and a regular
point, and `y∗` is its multiplier (`S∗ R∗ = 0`, `S∗ = C − ∑ᵢ y∗ᵢ Aᵢ`), then `S∗ • (D Dᵀ) ≥ 0` (11)
for every `D ∈ ℝ^{n×r}` with `Aᵢ R∗ • D = 0` for all `i` (12). -/
theorem prop_2_3_second_order {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) (hsa : StandingAssumptions C A b) {r : ℕ} (hr0 : 0 < r)
    (hrn : r ≤ n) (R : Matrix (Fin n) (Fin r) ℝ) (hloc : IsNrLocalMin C A b R)
    (hreg : IsRegular A R) (y : Fin m → ℝ) (hy : slack C A y * R = 0)
    (D : Matrix (Fin n) (Fin r) ℝ) (hD : ∀ i, frob (A i * R) D = 0) :
    0 ≤ frob (slack C A y) (D * Dᵀ) := by sorry

end BurerMonteiro.RankIncrease
