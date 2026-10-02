-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialB_prop_2_4_offdiag_diagdom_psd
-- name    : DiscreteConvex.CombinatorialB.prop_2_4_offdiag_diagdom_psd
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:32:36.608846+00:00
-- url     : https://prove2.me/theorems/7ab1921e-2dd4-47d3-8c0b-4bfa6e00ab83
-- title:
--   Proposition 2.4 -- off-diagonal nonpositivity + diagonal dominance implies PSD
-- statement:
--   A symmetric matrix $L$ with off-diagonal nonpositivity (2.9) and diagonal dominance (2.10) is positive semidefinite.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.64, Proposition 2.4.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.64, Proposition 2.4

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_OffDiagNonpos
import Definitions.Def_DiscreteConvex_CombinatorialB_DiagDominance

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.64, Proposition 2.4, in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Proposition 2.4.** A symmetric matrix `L` with off-diagonal nonpositivity (2.9) and
diagonal dominance (2.10) is positive semidefinite. -/
theorem prop_2_4_offdiag_diagdom_psd {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ) (hsymm : L.IsSymm) (h9 : OffDiagNonpos L) (h10 : DiagDominance L) :
    L.PosSemidef := by sorry

end DiscreteConvex.CombinatorialB
