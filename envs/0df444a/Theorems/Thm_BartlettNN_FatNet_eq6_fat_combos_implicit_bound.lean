-- Prove2me | Theorems.Thm_BartlettNN_FatNet_eq6_fat_combos_implicit_bound
-- name    : BartlettNN.FatNet.eq6_fat_combos_implicit_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:48:49.523726+00:00
-- url     : https://prove2.me/theorems/b717a756-2dae-4353-ad81-71d1b2c096e6
-- title:
--   Eq. (6) — m ≤ (64M²A²/γ²)(3 + d log₂(8emMA/γ) log₂(36mM²A²/γ²)) for m = fat_H(4γ)
-- statement:
--   Let $F$ be a nonempty class of functions from a set $X$ to $[-M/2,M/2]$, let $M,A,\gamma>0$, and let $H$ be the class of two-layer networks $\sum_iw_if_i$ with $f_i\in F$ and $\sum_i|w_i|\le A$ (Theorem 17). Suppose $m=\operatorname{fat}_H(4\gamma)$ and $d=\operatorname{fat}_F(\gamma/(8A))$ are finite and
--
--   $$
--   m\ \ge\ 2+2d\log_2(64MA/\gamma).
--   $$
--
--   Then
--
--   $$
--   m\ \le\ \frac{64M^2A^2}{\gamma^2}\Big(3+d\,\log_2\!\Big(\frac{8emMA}{\gamma}\Big)\log_2\!\Big(\frac{36mM^2A^2}{\gamma^2}\Big)\Big).
--   \tag{6}
--   $$
--
--   This is the explicit form of Theorem 17 before the inequality is solved for $m$; the paper derives it from Lemmas 19, 20 and 22.
--
--   **Formalization Note** $M,A,\gamma>0$ are implicit in the logarithms and in $\gamma/(8A)$. Logarithms are base $2$ and $e=\exp(1)$. The second logarithm's argument is printed as $8emMA/\gamma$ (no $d$ in the denominator, unlike Lemma 20) and is copied as printed.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 533, proof of Theorem 17, Eq. (6)

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_FatNet_combos

namespace BartlettNN.FatNet

/-- **Inequality (6)** (proof of Theorem 17, Bartlett 1998, p. 533).
For the classes of Theorem 17 (`F` nonempty, `[−M/2, M/2]`-valued, `H = combos F A`), with
`M, A, γ > 0`: if `m = fat_H(4γ)` and `d = fat_F(γ/(8A))` are finite and
`m ≥ 2 + 2d log₂(64MA/γ)`, then
`m ≤ (64M²A²/γ²)(3 + d log₂(8emMA/γ) log₂(36mM²A²/γ²))`. -/
theorem eq6_fat_combos_implicit_bound {X : Type*} (F : Set (X → ℝ)) (M A γ : ℝ) (m d : ℕ)
    (hFne : F.Nonempty) (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hM : 0 < M) (hA : 0 < A) (hγ : 0 < γ)
    (hm : BartlettNN.Margin.fat (combos F A) (4 * γ) = m) (hd : BartlettNN.Margin.fat F (γ / (8 * A)) = d)
    (hmd : 2 + 2 * (d : ℝ) * Real.logb 2 (64 * M * A / γ) ≤ (m : ℝ)) :
    (m : ℝ) ≤ 64 * M ^ 2 * A ^ 2 / γ ^ 2 *
      (3 + (d : ℝ) * Real.logb 2 (8 * Real.exp 1 * m * M * A / γ) *
        Real.logb 2 (36 * m * M ^ 2 * A ^ 2 / γ ^ 2)) := by sorry

end BartlettNN.FatNet
