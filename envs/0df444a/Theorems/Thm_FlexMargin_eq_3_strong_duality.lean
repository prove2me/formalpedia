-- Prove2me | Theorems.Thm_FlexMargin_eq_3_strong_duality
-- name    : FlexMargin.eq_3_strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:42:10.488103+00:00
-- url     : https://prove2.me/theorems/cb95d3f0-4ba1-4d5d-9821-c75ba37bf451
-- title:
--   Display (3): strong duality for the maximum profit
-- statement:
--   Let $C\ge0$ be the plant capacities, $p$ the product margins, $\mathcal A$ a design and $d\in\mathbb R^n_+$ a demand vector. Then the maximum profit (1) equals the optimal value of the dual problem
--
--   $$
--   g(\mathcal A,d)=\min_{y,z}\ \sum_{i=1}^n d_i y_i+\sum_{j=1}^m C_j z_j\quad\text{s.t.}\quad y_i+z_j\ge p_i\ \ \forall(a_j,b_i)\in\mathcal A,\quad y\ge0,\quad z\ge0, \tag{3}
--   $$
--
--   and the minimum is attained. The dual prices are the starting point of the DMGI.
--
--   Differences from the source:
--   - encoding: capacities C_j (sign not stated) → hypothesis 0 ≤ C j; reason: with a negative capacity the LP (1) is infeasible and g is undefined; only excludes undefined cases
--   - encoding: margins p_i ∈ {P_1, …, P_T} → an arbitrary margin vector p : Fin n → ℝ; reason: every vector is P∘cat for the system whose margins are its distinct values; same instances
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §3.1, display (3), p. 16

import Mathlib
import Definitions.Def_FlexMargin_lpValue
import Definitions.Def_FlexMargin_IsDualFeasible

namespace FlexMargin

/-- **Display (3): LP strong duality for the maximum profit.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §3.1, display (3), p. 16: "Recall that for any demand instance d ∈ R^n_+, the maximum profit
achieved by flexibility design A, g(A,d), can be computed by solving (1). By strong duality theorem, we
have g(A,d) = min_{y,z} Σ_{i=1}^n di yi + Σ_{j=1}^m Cj zj s.t. yi + zj ≥ pi, ∀(aj,bi) ∈ A, yi ≥ 0,
∀1 ≤ i ≤ n, zj ≥ 0, ∀1 ≤ j ≤ m".

For capacities `C ≥ 0`, any margins `p`, any design `A` and any demand `d ≥ 0`: `g(A, d)`
(`FlexMargin.lpValue`) is the infimum of the dual objective over the dual feasible set
(`FlexMargin.IsDualFeasible`), and the infimum is attained (the page's "min").

**Formalization Note.** The capacities are nonnegative (a negative capacity makes (1) infeasible).
The margins are an arbitrary vector `p`, i.e. `p_i = P (cat i)` for the paper's system. -/
theorem eq_3_strong_duality {m n : ℕ} (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (p : Fin n → ℝ)
    (A : Finset (Fin m × Fin n)) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    lpValue C p A d =
        sInf {v : ℝ | ∃ (y : Fin n → ℝ) (z : Fin m → ℝ), IsDualFeasible p A y z ∧
          v = ∑ i, d i * y i + ∑ j, C j * z j} ∧
      ∃ (y : Fin n → ℝ) (z : Fin m → ℝ), IsDualFeasible p A y z ∧
        ∑ i, d i * y i + ∑ j, C j * z j = lpValue C p A d := by sorry

end FlexMargin
