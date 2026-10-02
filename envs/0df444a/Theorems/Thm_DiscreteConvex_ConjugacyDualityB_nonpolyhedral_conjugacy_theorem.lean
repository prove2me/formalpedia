-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_nonpolyhedral_conjugacy_theorem
-- name    : DiscreteConvex.ConjugacyDualityB.nonpolyhedral_conjugacy_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:35:15.85199+00:00
-- url     : https://prove2.me/theorems/4b4204f1-30ca-487a-abaa-4a6af8bbbca3
-- title:
--   Theorem 8.6 -- nonpolyhedral_conjugacy_theorem
-- statement:
--   **Theorem 8.6** (p.210). A closed proper convex function $f$ satisfies (M-EXC[R]) if and only if $f=g^\bullet$ for a closed proper convex function $g$ satisfying (SBF[R]) and (TRF[R]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210, Theorem 8.6.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210, Theorem 8.6

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SBFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_TRFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsClosedProperConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateRW

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.6 (p.210). A closed proper convex function satisfies (M-EXC[R]) iff it is the
conjugate of a closed proper convex function satisfying (SBF[R]) and (TRF[R]). -/
theorem nonpolyhedral_conjugacy_theorem (f : (V → ℝ) → WithTop ℝ) (hf : IsClosedProperConvex f) :
    MExchangeAxiomR f ↔
      ∃ g : (V → ℝ) → WithTop ℝ, IsClosedProperConvex g ∧ SBFR g ∧ TRFR g ∧
        f = ConvexConjugateRW g := by sorry

end DiscreteConvex.ConjugacyDualityB
