-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_mnat_lnat_ineq_extends_to_reals
-- name    : DiscreteConvex.ConjugacyDualityB.mnat_lnat_ineq_extends_to_reals
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:34:54.608222+00:00
-- url     : https://prove2.me/theorems/f42c8066-10c2-44d8-87ae-3700757ed285
-- title:
--   Proposition 8.14 -- mnat_lnat_ineq_extends_to_reals
-- statement:
--   **Proposition 8.14** (p.217). (1) If $f,-h\in M^\natural[\mathbb Z\to\mathbb R]$, $f(x)\ge h(x)$ for all $x\in\mathbb Z^V$ implies $\bar f(x)\ge\bar h(x)$ for all $x\in\mathbb R^V$. (2) The L$^\natural$ analogue.
--
--   **Formalization Note.** The inequality $f\ge h$ (with $h$ concave, possibly $-\infty$-valued) is restated as $f+h_2\ge 0$ where $h_2=-h$ is the M$^\natural$-convex function the book itself hypothesizes, avoiding any need for `WithTop ℝ` negation or an `EReal`-valued codomain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.217, Proposition 8.14.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.217, Proposition 8.14

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexClosureVal

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.14 (p.217). An inequality between M♮-(resp. L♮-)convex functions on the
integer lattice extends to the real domain via convex/concave closure. -/
theorem mnat_lnat_ineq_extends_to_reals :
    (∀ f h2 : (V → ℤ) → WithTop ℝ, MNaturalConvex f → MNaturalConvex h2 →
      (∀ x : V → ℤ, f x + h2 x ≥ 0) →
      ∀ x : V → ℝ, ConvexClosureVal f x + ConvexClosureVal h2 x ≥ 0) ∧
    (∀ g k2 : (V → ℤ) → WithTop ℝ, LNaturalConvex g → LNaturalConvex k2 →
      (∀ p : V → ℤ, g p + k2 p ≥ 0) →
      ∀ p : V → ℝ, ConvexClosureVal g p + ConvexClosureVal k2 p ≥ 0) := by sorry

end DiscreteConvex.ConjugacyDualityB
