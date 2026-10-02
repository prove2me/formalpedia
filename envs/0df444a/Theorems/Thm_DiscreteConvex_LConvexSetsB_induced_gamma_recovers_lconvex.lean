-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexSetsB_induced_gamma_recovers_lconvex
-- name    : DiscreteConvex.LConvexSetsB.induced_gamma_recovers_lconvex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:44:35.003612+00:00
-- url     : https://prove2.me/theorems/ee6957ae-23c8-4339-8648-de29eb9804d4
-- title:
--   Proposition 5.4 -- induced_gamma_recovers_lconvex
-- statement:
--   **Proposition 5.4** (p.124), the converse of Proposition 5.3. For an integer-valued distance function $\gamma$, $D = D(\gamma) \cap \mathbb Z^V$ is an L-convex set provided $D(\gamma)$ is nonempty. The triangle inequality is not assumed here.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.124, Proposition 5.4.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.124, Proposition 5.4

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_DistanceFunction
import Definitions.Def_DiscreteConvex_LConvexSetsB_IsIntegerValuedGamma
import Definitions.Def_DiscreteConvex_LConvexSetsB_AdmissiblePotentials
import Definitions.Def_DiscreteConvex_LConvexSetsB_LConvexSet

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.124, Proposition 5.4, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- Proposition 5.4 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.124). See the item's
`natural_language_statement` for the full statement. -/
theorem induced_gamma_recovers_lconvex {V : Type*} [Fintype V] [DecidableEq V]
    (γ : V → V → WithTop ℝ) (hγ : DistanceFunction γ) (hInt : IsIntegerValuedGamma γ)
    (hne : (AdmissiblePotentials γ).Nonempty) :
    LConvexSet {p : V → ℤ | (fun v => (p v : ℝ)) ∈ AdmissiblePotentials γ} := by sorry

end DiscreteConvex.LConvexSetsB
