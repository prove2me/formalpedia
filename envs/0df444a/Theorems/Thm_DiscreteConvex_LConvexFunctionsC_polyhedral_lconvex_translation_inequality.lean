-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_polyhedral_lconvex_translation_inequality
-- name    : DiscreteConvex.LConvexFunctionsC.polyhedral_lconvex_translation_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:35:09.285393+00:00
-- url     : https://prove2.me/theorems/17e9b2b2-68af-448b-99fe-912eb29927c8
-- title:
--   Theorem 7.29 -- polyhedral_lconvex_translation_inequality
-- statement:
--   **Theorem 7.29** (p.192). A polyhedral L-convex function $g\in L[\mathbb R\to\mathbb R]$ satisfies $g(p)+g(q)\ge g((p-\alpha\mathbf 1)\vee q)+g(p\wedge(q+\alpha\mathbf 1))$ for all $p,q\in\mathbb R^V$ and $\alpha\in\mathbb R$, Eq. (7.32).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, Theorem 7.29.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, Theorem 7.29

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.29 (p.192). A polyhedral L-convex function satisfies the translation inequality for
every `α ∈ R`, Eq. (7.32). -/
theorem polyhedral_lconvex_translation_inequality (g : (V → ℝ) → WithTop ℝ) (hg : SBFR g ∧ TRFR g) :
    ∀ p q : V → ℝ, ∀ alpha : ℝ,
      g p + g q ≥ g (fun v => max (p v - alpha) (q v)) + g (fun v => min (p v) (q v + alpha)) := by sorry

end DiscreteConvex.LConvexFunctionsC
