-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_submodular_minimizer_criterion
-- name    : DiscreteConvex.LConvexFunctionsB.submodular_minimizer_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:22:15.571847+00:00
-- url     : https://prove2.me/theorems/b5e7ec5a-cc40-4916-86e7-4887aee5812b
-- title:
--   Theorem 7.15 -- submodular_minimizer_criterion
-- statement:
--   **Theorem 7.15** (p.185). Let $\rho$ be a submodular set function. A subset $X\in\operatorname{dom}\rho$ is a minimizer of $\rho$ if and only if $\rho(X)\le\rho(Y)$ for any $Y$ that includes $X$ or is included in $X$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.185, Theorem 7.15.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.185, Theorem 7.15

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_Submodular

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.15 (p.185). A submodular set function's global minimizer is characterized by local
optimality against comparable sets. Submodularity is the page's hypothesis and is what makes the
local test global: on `V = {a,b}` with `ρ(∅) = 5`, `ρ({a}) = 0`, `ρ({b}) = -1`, `ρ(V) = 5` the
local conditions hold at `{a}` while `{b}` has the smaller value. -/
theorem submodular_minimizer_criterion (rho : Finset V → WithTop ℝ) (hrho : Submodular rho)
    (X : Finset V) (hX : rho X ≠ ⊤) :
    (∀ Y : Finset V, rho X ≤ rho Y) ↔
      (∀ Y : Finset V, (X ⊆ Y ∨ Y ⊆ X) → rho X ≤ rho Y) := by sorry

end DiscreteConvex.LConvexFunctionsB
