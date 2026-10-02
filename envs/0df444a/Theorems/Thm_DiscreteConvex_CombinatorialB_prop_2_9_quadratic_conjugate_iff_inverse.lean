-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialB_prop_2_9_quadratic_conjugate_iff_inverse
-- name    : DiscreteConvex.CombinatorialB.prop_2_9_quadratic_conjugate_iff_inverse
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:33:07.228544+00:00
-- url     : https://prove2.me/theorems/5ddc2d11-dc3d-4340-9c4e-977185a64515
-- title:
--   Proposition 2.9 -- conjugate quadratic forms correspond to inverse matrices
-- statement:
--   Let $M,L$ be positive-definite symmetric matrices. $f(x)=\tfrac12x^\top Mx$ and $g(p)=\tfrac12p^\top Lp$ are Legendre-Fenchel conjugate to each other if and only if $M$ and $L$ are inverse to each other.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68, Proposition 2.9.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68, Proposition 2.9

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_QF
import Definitions.Def_DiscreteConvex_CombinatorialB_Conjugate

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.68, Proposition 2.9, in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Proposition 2.9.** Let `M, L` be positive-definite symmetric matrices. The quadratic
forms `f(x) = (1/2)x⊤Mx` and `g(p) = (1/2)p⊤Lp` are conjugate to each other with respect to
the Legendre-Fenchel transformation (1.6) if and only if `M` and `L` are inverse to each other. -/
theorem prop_2_9_quadratic_conjugate_iff_inverse {V : Type*} [Fintype V] [DecidableEq V]
    (M L : Matrix V V ℝ) (hMsymm : M.IsSymm) (hLsymm : L.IsSymm) (hMpd : M.PosDef)
    (hLpd : L.PosDef) :
    ((∀ p : V → ℝ, Conjugate (QF M) p = ((QF L p : ℝ) : EReal)) ∧
      (∀ x : V → ℝ, Conjugate (QF L) x = ((QF M x : ℝ) : EReal))) ↔ M * L = 1 := by sorry

end DiscreteConvex.CombinatorialB
