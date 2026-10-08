-- Prove2me | Theorems.Thm_BartlettNN_FatNet_theorem17_fat_combos_bound
-- name    : BartlettNN.FatNet.theorem17_fat_combos_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:48:49.761914+00:00
-- url     : https://prove2.me/theorems/7257836e-13cc-463e-97a8-3fef3f1f1450
-- title:
--   Theorem 17 — fat_H(γ) ≤ (cM²A²d/γ²) log²(MAd/γ) for ℓ1-bounded two-layer networks, d = fat_F(γ/(32A))
-- statement:
--   There is a universal constant $c>0$ with the following property. Let $F$ be a nonempty class of functions from a set $X$ to $[-M/2,M/2]$. For $A>0$ let
--
--   $$
--   H=\Big\{\sum_{i=1}^N w_if_i:\ N\in\mathbb N,\ f_i\in F,\ \sum_{i=1}^N|w_i|\le A\Big\}
--   $$
--
--   be the class of two-layer networks with hidden units from $F$. Let $\gamma>0$ be such that $d=\operatorname{fat}_F(\gamma/(32A))$ is a natural number with $d\ge1$. Then $\operatorname{fat}_H(\gamma)$ is finite and
--
--   $$
--   \operatorname{fat}_H(\gamma)\ \le\ \frac{cM^2A^2d}{\gamma^2}\,\ln^2\!\Big(\frac{MAd}{\gamma}\Big).
--   $$
--
--   The bound does not depend on the number $N$ of hidden units: the capacity of the network class at scale $\gamma$ is governed by the $\ell_1$ size $A$ of the output weights and the capacity of the hidden units at the finer scale $\gamma/(32A)$. Combined with the margin bound of Theorem 2, this gives generalization bounds for networks with small weights regardless of their size.
--
--   **Formalization Note** The constant $c$ is universal: it is quantified before the input space $X$, the class $F$ and the parameters $M,A,\gamma,d$. The conclusion asserts that $\operatorname{fat}_H(\gamma)$ equals a natural number $k$ obeying the bound, so finiteness is part of the claim. Two corrections of the printed statement: the paper writes $\gamma\ge0$, but at $\gamma=0$ the right side is undefined while $\operatorname{fat}_H(0)\ge1$, so $\gamma>0$ is stated; the paper writes $A\ge0$, but $\gamma/(32A)$ is undefined at $A=0$ (where $H=\{0\}$ and the claim is empty), so $A>0$ is stated. The paper's bare $\log$ is the natural logarithm here; the base only rescales $c$. $X$ ranges over types in the lowest universe.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 532, Theorem 17

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_FatNet_combos

namespace BartlettNN.FatNet

/-- **Theorem 17** (Bartlett 1998, p. 532).
There is a universal constant `c > 0` such that the following holds. Let `F` be a nonempty class
of functions from `X` to `[−M/2, M/2]`, let `A > 0`, and let `H = combos F A` be the class of
two-layer networks `∑ w_i f_i` with `f_i ∈ F` and `∑ |w_i| ≤ A`. If `γ > 0` and
`d = fat_F(γ/(32A)) ≥ 1`, then `fat_H(γ)` is finite and
`fat_H(γ) ≤ (c M² A² d / γ²) ln²(MAd/γ)`.
The constant `c` is quantified before the input space, the classes and every parameter.
Corrections of the printed statement: `γ > 0` (printed `γ ≥ 0`, under which the bound is
meaningless) and `A > 0` (printed `A ≥ 0`, under which `γ/(32A)` is undefined). -/
theorem theorem17_fat_combos_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ {X : Type} (F : Set (X → ℝ)) (M A γ : ℝ) (d : ℕ),
      F.Nonempty → (∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2)) → 0 < A → 0 < γ →
      BartlettNN.Margin.fat F (γ / (32 * A)) = d → 1 ≤ d →
      ∃ k : ℕ, BartlettNN.Margin.fat (combos F A) γ = k ∧
        (k : ℝ) ≤ c * M ^ 2 * A ^ 2 * d / γ ^ 2 * (Real.log (M * A * d / γ)) ^ 2 := by sorry

end BartlettNN.FatNet
