-- Prove2me | Theorems.Thm_DrinfeldCurve_LocalChart_card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq
-- name    : DrinfeldCurve.LocalChart.card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/0dc1973d-4f45-583f-b944-7d67765e8ace
-- title:
--   Drinfeld form as a product of q+1 linear forms
-- statement:
--   Let $q$ be a prime, let $W$ be a nontrivial commutative ring, and let $T$ be a finite subset of $W$ such that $\prod_{t\in T}(X - t) = X^{q} - X$ in $W[X]$. Three conclusions are asserted. First, $T$ has exactly $q$ elements. Second, index linear forms by $i \in \mathrm{Option}\,T$, assigning to the base point $\mathrm{none}$ the coefficient pair $(1,0)$ and to $\mathrm{some}\,t$ the pair $(-t,1)$; then in the two-variable power series ring $W[[X_0,X_1]]$ (formal power series in `Fin 2` variables) the product $\prod_i (a_i X_0 + b_i X_1)$, with coefficients inserted by the constant embedding, equals [`DrinfeldCurve.LocalChart.drinfeldForm q W`](def/DrinfeldCurve_LocalChart.html#L18), which is by definition $X_0 X_1^{q} - X_0^{q} X_1$. Third, under the additional hypothesis that $t - t'$ is a unit of $W$ for all distinct $t, t' \in T$, the determinant $a_i b_j - a_j b_i$ is a unit of $W$ for all $i \neq j$ in $\mathrm{Option}\,T$.
--
--   This identifies the $q+1$ branches of the Drinfeld form $X_0X_1^{q} - X_0^{q}X_1$, the local equation at a supersingular point of a modular curve with full level structure, with the lines of $\mathbb{P}^1(\mathbb{F}_q)$ lifted through a full set $T$ of Teichmüller representatives, the pairwise unimodularity expressing that the branches have distinct tangent directions. It feeds the local analysis of the chart: the branch primes attached to a power series congruent to the Drinfeld form, and the discrete valuation ring property of the corresponding quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_LocalChart_card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem DrinfeldCurve.LocalChart.card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq
    (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [Nontrivial W]
    (T : Finset W) (hT : ∏ t ∈ T, (Polynomial.X - Polynomial.C t) = (Polynomial.X ^ q - Polynomial.X : Polynomial W)) :
    T.card = q ∧
    (∏ i : Option ↥T,
        (MvPowerSeries.C (Option.elim i (1 : W) (fun t => -(t : W))) * MvPowerSeries.X 0 +
          MvPowerSeries.C (Option.elim i (0 : W) (fun _ => (1 : W))) * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W)) =
      DrinfeldCurve.LocalChart.drinfeldForm q W ∧
    ((∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → IsUnit (t - t')) →
      ∀ i j : Option ↥T, i ≠ j →
        IsUnit (Option.elim i (1 : W) (fun t => -(t : W)) * Option.elim j (0 : W) (fun _ => (1 : W)) -
          Option.elim j (1 : W) (fun t => -(t : W)) * Option.elim i (0 : W) (fun _ => (1 : W)))) := by sorry
