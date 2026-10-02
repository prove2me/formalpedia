-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialB_prop_2_14_principal_submatrix_in_Linv
-- name    : DiscreteConvex.CombinatorialB.prop_2_14_principal_submatrix_in_Linv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:34:49.148147+00:00
-- url     : https://prove2.me/theorems/0c4e2d3e-769a-48af-b7c0-6df6b521e555
-- title:
--   Proposition 2.14 -- principal submatrices of L-inverse matrices are L-inverse
-- statement:
--   Any principal submatrix of $M\in\mathcal L^{-1}$ belongs to $\mathcal L^{-1}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.72, Proposition 2.14.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.72, Proposition 2.14

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_MemLInv

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.72, Proposition 2.14, in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Proposition 2.14.** Any principal submatrix of `M ∈ L⁻¹` belongs to `L⁻¹`. -/
theorem prop_2_14_principal_submatrix_in_Linv {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : MemLInv M) (S : Finset V) :
    MemLInv (M.submatrix ((↑) : {x // x ∈ S} → V) ((↑) : {x // x ∈ S} → V)) := by sorry

end DiscreteConvex.CombinatorialB
