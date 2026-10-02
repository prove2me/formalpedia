-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialB_theorem_2_12_nine_conditions_equivalent
-- name    : DiscreteConvex.CombinatorialB.theorem_2_12_nine_conditions_equivalent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:35:07.959337+00:00
-- url     : https://prove2.me/theorems/0032140e-d4d1-4bec-9456-f997c74e2bf9
-- title:
--   Theorem 2.12 -- nine equivalent characterizations of L-inverse matrices
-- statement:
--   For an $n\times n$ nonsingular symmetric matrix $M$, nine conditions (a),(b),(b+),(c),(c+),(d),(d+),(e),(e+) -- membership in $\mathcal L^{-1}$, two sign-consistency inequalities and their strict forms, two directional-derivative exchange conditions and their strict forms, and the exchange property $(\mathrm{M}^\natural\text{-EXC}[\mathbb R])$ and its strict form -- are all equivalent.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.70-71, Theorem 2.12.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.70-71, Theorem 2.12

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_MemLInv
import Definitions.Def_DiscreteConvex_CombinatorialB_CondB
import Definitions.Def_DiscreteConvex_CombinatorialB_CondBPlus
import Definitions.Def_DiscreteConvex_CombinatorialB_CondC
import Definitions.Def_DiscreteConvex_CombinatorialB_CondCPlus
import Definitions.Def_DiscreteConvex_CombinatorialB_CondD
import Definitions.Def_DiscreteConvex_CombinatorialB_CondDPlus
import Definitions.Def_DiscreteConvex_CombinatorialB_QF
import Definitions.Def_DiscreteConvex_CombinatorialB_MNatExchangeR
import Definitions.Def_DiscreteConvex_CombinatorialB_MNatExchangePlusR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, pp.70-71, Theorem 2.12, in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Theorem 2.12.** For an `n×n` nonsingular symmetric matrix `M`, the nine conditions
(a), (b), (b+), (c), (c+), (d), (d+), (e), (e+) are all equivalent. -/
theorem theorem_2_12_nine_conditions_equivalent {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hsymm : M.IsSymm) (hnonsing : M.det ≠ 0) :
    List.TFAE [MemLInv M, CondB M, CondBPlus M, CondC M, CondCPlus M, CondD M, CondDPlus M,
      MNatExchangeR (QF M), MNatExchangePlusR (QF M)] := by sorry

end DiscreteConvex.CombinatorialB
