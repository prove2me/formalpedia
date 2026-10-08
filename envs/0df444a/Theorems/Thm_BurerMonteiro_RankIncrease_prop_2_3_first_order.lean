-- Prove2me | Theorems.Thm_BurerMonteiro_RankIncrease_prop_2_3_first_order
-- name    : BurerMonteiro.RankIncrease.prop_2_3_first_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:39:09.592411+00:00
-- url     : https://prove2.me/theorems/32512da4-f8ad-42eb-933b-648e493c1e69
-- title:
--   Proposition 2.3 (first-order part): a unique multiplier $y^*$ with $S^*R^*=0$
-- statement:
--   Let $C, A_1,\dots,A_m\in\mathcal S^n$ be symmetric and $b\in\mathbb R^m$, under the standing assumptions of §2.1, and let $r$ be a positive integer with $r\le n$. Let $R^*\in\mathbb R^{n\times r}$ be a local minimum of $(N_r)$ which is a regular point, i.e. the constraint gradients $A_1R^*,\dots,A_mR^*$ are linearly independent. Then there is a **unique** $y^*\in\mathbb R^m$ such that the matrix $S^*=C-\sum_{i=1}^m y^*_iA_i$ satisfies
--   $$S^*R^*=0.\tag{10}$$
--
--   This is the first-order necessary condition (Lagrange multiplier rule) for $(N_r)$, written through (9). Uniqueness of the multiplier is what lets the proof of Proposition 2.5 identify the multiplier at $\hat R$ with the one at $R^*$.
--
--   **Formalization Note** A local minimum is a feasible point minimizing the objective over nearby feasible points. The standing assumptions and the bound $r\le n$ are carried as on the page although the argument does not use them.
-- source:
--   Burer & Monteiro, A nonlinear programming algorithm for solving semidefinite programs via low-rank factorization (manuscript of March 9, 2001; Math. Program. 95 (2003)), p. 6, Proposition 2.3, Eq. (10)

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

open Matrix
open scoped Matrix.Norms.Frobenius

namespace BurerMonteiro.RankIncrease

/-- Proposition 2.3, first-order part (p. 6): if `R∗` is a local minimum of `(N_r)` and a regular
point, there is a unique Lagrange multiplier `y∗ ∈ ℝᵐ` whose `S∗ = C − ∑ᵢ y∗ᵢ Aᵢ` satisfies
`S∗ R∗ = 0` (10). -/
theorem prop_2_3_first_order {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) (hsa : StandingAssumptions C A b) {r : ℕ} (hr0 : 0 < r)
    (hrn : r ≤ n) (R : Matrix (Fin n) (Fin r) ℝ) (hloc : IsNrLocalMin C A b R)
    (hreg : IsRegular A R) :
    ∃! y : Fin m → ℝ, slack C A y * R = 0 := by sorry

end BurerMonteiro.RankIncrease
