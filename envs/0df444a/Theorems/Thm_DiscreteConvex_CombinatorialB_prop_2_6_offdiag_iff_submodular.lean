-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialB_prop_2_6_offdiag_iff_submodular
-- name    : DiscreteConvex.CombinatorialB.prop_2_6_offdiag_iff_submodular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:32:56.89779+00:00
-- url     : https://prove2.me/theorems/52e6e232-6a73-4806-bf30-6dfab9ed652a
-- title:
--   Proposition 2.6 -- off-diagonal nonpositivity iff submodularity of the quadratic form
-- statement:
--   For a symmetric matrix $L$, off-diagonal nonpositivity (2.9) is equivalent to submodularity (2.17) of $g(p)=\tfrac12p^\top Lp$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.65, Proposition 2.6.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.65, Proposition 2.6

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_OffDiagNonpos
import Definitions.Def_DiscreteConvex_CombinatorialB_QF
import Definitions.Def_DiscreteConvex_CombinatorialB_Submodular

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.65, Proposition 2.6, in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Proposition 2.6.** For a symmetric matrix `L`, off-diagonal nonpositivity (2.9) is
equivalent to submodularity (2.17) of the associated quadratic form `g(p) = (1/2)p⊤Lp`. -/
theorem prop_2_6_offdiag_iff_submodular {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ) (hsymm : L.IsSymm) :
    OffDiagNonpos L ↔ Submodular (QF L) := by sorry

end DiscreteConvex.CombinatorialB
