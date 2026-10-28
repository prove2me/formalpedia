-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RatioProductAccuracy_ratio_product_accuracy
-- name    : CountingMatroid.Analysis.RatioProductAccuracy.ratio_product_accuracy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:03:22.719036+00:00
-- url     : https://prove2.me/theorems/f55c648f-57a0-45c5-8b9e-41dc5580ff5b
-- title:
--   Phasewise ratio accuracy controls the final product
-- statement:
--   Let $L\in\mathbb N$, let rational $0<\varepsilon<1$, and let $C,R:\mathbb N\to\mathbb Q$. Assume $C(j)>0$ for every natural $j$. Set $\eta=\varepsilon/(32(L+1))$, and suppose that for every $0\le j<L$, $$\frac{1-\eta}{1+\eta}\le\frac{R(j)}{C(j+1)/C(j)}\le\frac{1+\eta}{1-\eta}.$$ Then $$\left(1-\frac{\varepsilon}{4}\right)C(L)\le C(0)\prod_{j=0}^{L-1}R(j)\le\left(1+\frac{\varepsilon}{4}\right)C(L).$$ The empty product for $L=0$ is one.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RatioProductAccuracy.lean#L66-L104

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace CountingMatroid.Analysis.RatioProductAccuracy
end CountingMatroid.Analysis.RatioProductAccuracy
set_option autoImplicit false

namespace CountingMatroid.Analysis.RatioProductAccuracy
end CountingMatroid.Analysis.RatioProductAccuracy
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RatioProductAccuracy

theorem CountingMatroid.Analysis.RatioProductAccuracy.ratio_product_accuracy (L : ℕ) (ε : ℚ) (C R : ℕ → ℚ)
    (hε : 0 < ε) (hεone : ε < 1) (hC : ∀ j, 0 < C j)
    (hR : ∀ j < L,
      (1 - ε / (32 * ((L : ℚ) + 1))) / (1 + ε / (32 * ((L : ℚ) + 1))) ≤
        R j / (C (j + 1) / C j) ∧
      R j / (C (j + 1) / C j) ≤
        (1 + ε / (32 * ((L : ℚ) + 1))) / (1 - ε / (32 * ((L : ℚ) + 1)))) :
    (1 - ε / 4) * C L ≤ C 0 * (∏ j ∈ Finset.range L, R j) ∧
      C 0 * (∏ j ∈ Finset.range L, R j) ≤ (1 + ε / 4) * C L := by sorry
