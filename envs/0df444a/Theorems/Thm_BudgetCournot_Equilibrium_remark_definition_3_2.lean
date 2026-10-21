-- Prove2me | Theorems.Thm_BudgetCournot_Equilibrium_remark_definition_3_2
-- name    : BudgetCournot.Equilibrium.remark_definition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:50.968985+00:00
-- url     : https://prove2.me/theorems/ea70450e-6f50-4dc3-87ba-73d3c7f04613
-- title:
--   Remark after Definition 3.2, p. 8 — H is continuous, non-increasing, piecewise linear, and H(𝔹_j) = R_j
-- statement:
--   Let $0\le R_1\le\cdots\le R_M$ and $\beta_1,\dots,\beta_M>0$, and let
--
--   $$H(x)=\inf\Big\{z\ge 0:\ \sum_{j=1}^M\beta_j(R_j-z)^+\le x\Big\},\qquad x\ge 0,$$
--
--   with cutoff budgets $\mathbb B_j=\sum_{k=j}^M\beta_k(R_k-R_j)$. Then on $[0,\infty)$:
--
--   1. $H$ is continuous;
--   2. $H$ is non-increasing;
--   3. $H$ is piecewise linear: there is a finite set $T$ of breakpoints such that $H$ is affine on every interval $[a,b]\subseteq[0,\infty)$ whose interior contains no point of $T$;
--   4. $H(\mathbb B_j)=R_j$ for every market $j$.
--
--   $H$ is the "water level" that turns augmented budgets into the levels of the closed form of Theorem 1; the last property links the cutoff budgets to the market sizes.
--
--   **Formalization Note** Only the market part of the standing assumptions is assumed. Piecewise linearity is stated as affinity on every interval free of breakpoints of a finite set.
-- source:
--   Caldentey & Haugh, Multimarket Cournot equilibria with heterogeneous resource-constrained firms, Operations Research (2024), author version of January 20, 2024, p. 8, remark after Definition 3.2

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace BudgetCournot.Equilibrium

/-- Remark after Definition 3.2, p. 8: on `x ≥ 0`, `H` is continuous, non-increasing and
piecewise linear (affine between consecutive points of a finite set), and `H(𝔹_j) = R_j`. -/
theorem remark_definition_3_2 {M : ℕ} (R β : Fin M → ℝ) (hR : Monotone R)
    (hR0 : ∀ j, 0 ≤ R j) (hβ : ∀ j, 0 < β j) :
    ContinuousOn (H R β) (Set.Ici 0) ∧ AntitoneOn (H R β) (Set.Ici 0) ∧
      (∃ T : Finset ℝ, ∀ a b : ℝ, 0 ≤ a → a ≤ b → (∀ t ∈ T, t ∉ Set.Ioo a b) →
        ∃ c d : ℝ, ∀ y ∈ Set.Icc a b, H R β y = c + d * y) ∧
      ∀ j, H R β (cutoffBudget R β j) = R j := by sorry

end BudgetCournot.Equilibrium
