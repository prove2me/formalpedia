-- Prove2me | Theorems.Thm_CuttingStock63_Fractional_column_choice_knapsack
-- name    : CuttingStock63.Fractional.column_choice_knapsack
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:06:59.688933+00:00
-- url     : https://prove2.me/theorems/5eb9732c-a9d9-4c32-9b49-9a378405b521
-- title:
--   Customer Tolerances, p. 883 — column choice for the ratio objective is again a knapsack problem (with Π̄ᵢ = −(z₁Π²ᵢ − z₂Π¹ᵢ − z₂lᵢ))
-- statement:
--   Fix a stock length $L$, piece lengths $l_1,\dots,l_m$, the current values $z_1,z_2$ of the two auxiliary objectives, and vectors $\Pi^1,\Pi^2\in\mathbb R^m$ (in the paper, the last $m$ entries of the first two rows $(1,0,\Pi^1)$ and $(0,1,\Pi^2)$ of the basis inverse). A cutting pattern is a vector $a\in\mathbb Z_{\ge0}^m$; its waste is $w=L-\sum_i a_il_i$ (eq. (4)) and its column is $c=(-w,-1,a)$. Consider the bracket of (5),
--   $$\Delta(a)=z_1\,(0,1,\Pi^2)\cdot c-z_2\,(1,0,\Pi^1)\cdot c=z_1\Big(-1+\sum_i\Pi^2_ia_i\Big)-z_2\Big(-w+\sum_i\Pi^1_ia_i\Big),$$
--   so that $d\zeta/dx_j=\Delta(a_j)/z_2^2$. Then:
--
--   1. (third line of (5)) $\Delta(a)=wz_2-z_1+\sum_i\big(z_1\Pi^2_i-z_2\Pi^1_i\big)a_i$;
--   2. (after substituting (4)) with $k=Lz_2-z_1$ and $\bar\Pi_i=-\big(z_1\Pi^2_i-z_2\Pi^1_i-z_2l_i\big)$,
--   $$\Delta(a)=k-\sum_i\bar\Pi_ia_i ;$$
--   3. if $z_2\ne0$, a pattern $a$ with $\sum_ia_il_i\le L$ minimizes $\Delta(a)/z_2^2$ over all patterns that fit in $L$ if and only if it maximizes $\sum_i\bar\Pi_ia_i$ subject to $\sum_ia_il_i\le L$, $a\in\mathbb Z^m_{\ge0}$.
--
--   Hence choosing the column with the most negative $d\zeta/dx_j$ is a knapsack problem with values $\bar\Pi_i$, exactly as for the linear objective of Part I; only the values change.
--
--   **Formalization Note** The page prints the coefficient $-l_i$ inside the sum after substituting (4), and $\bar\Pi_i=-(z_1\Pi^2_i-z_2\Pi^1_i-l_i)$. Substituting $w=L-\sum_ia_il_i$ into $wz_2$ gives $Lz_2-z_2\sum_ia_il_i$, so the correct coefficient is $-z_2l_i$; the statement uses the corrected one (the two agree when $z_2=1$). The identities hold for arbitrary $\Pi^1,\Pi^2$, in particular for the rows of any basis inverse.
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 883, Customer Tolerances, eq. (5) second and third lines, the substitution of (4), and "So column choice is again a knapsack problem" (coefficient −l_i corrected to −z_2 l_i)

import Mathlib

namespace CuttingStock63.Fractional
theorem column_choice_knapsack {m : ℕ} (L z₁ z₂ : ℝ) (l p₁ p₂ : Fin m → ℝ) :
    (∀ a : Fin m → ℕ,
      z₁ * (-1 + ∑ i, p₂ i * a i) - z₂ * (-(L - ∑ i, (a i : ℝ) * l i) + ∑ i, p₁ i * a i) =
        (L - ∑ i, (a i : ℝ) * l i) * z₂ - z₁ + ∑ i, (z₁ * p₂ i - z₂ * p₁ i) * a i) ∧
    (∀ a : Fin m → ℕ,
      z₁ * (-1 + ∑ i, p₂ i * a i) - z₂ * (-(L - ∑ i, (a i : ℝ) * l i) + ∑ i, p₁ i * a i) =
        (L * z₂ - z₁) - ∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * a i) ∧
    (z₂ ≠ 0 → ∀ a : Fin m → ℕ, ∑ i, (a i : ℝ) * l i ≤ L →
      ((∀ a' : Fin m → ℕ, ∑ i, (a' i : ℝ) * l i ≤ L →
          (z₁ * (-1 + ∑ i, p₂ i * a i) - z₂ * (-(L - ∑ i, (a i : ℝ) * l i) + ∑ i, p₁ i * a i)) /
              z₂ ^ 2 ≤
            (z₁ * (-1 + ∑ i, p₂ i * a' i) -
                z₂ * (-(L - ∑ i, (a' i : ℝ) * l i) + ∑ i, p₁ i * a' i)) / z₂ ^ 2) ↔
        (∀ a' : Fin m → ℕ, ∑ i, (a' i : ℝ) * l i ≤ L →
          ∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * a' i ≤
            ∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * a i))) := by sorry
end CuttingStock63.Fractional
