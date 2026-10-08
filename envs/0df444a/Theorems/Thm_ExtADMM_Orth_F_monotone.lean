-- Prove2me | Theorems.Thm_ExtADMM_Orth_F_monotone
-- name    : ExtADMM.Orth.F_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:23.708551+00:00
-- url     : https://prove2.me/theorems/f40dfb40-c6d3-4907-b909-13f079b046a2
-- title:
--   p. 5 — the affine map F is monotone
-- statement:
--   Let $F$ be the affine four-block map in (2.5c), with first three blocks $-A_i^T\lambda$ and last block $A_1x_1+A_2x_2+A_3x_3-b$. For any four-block points $w,w'$, it is monotone:
--
--   $$ (w-w')^T(F(w)-F(w'))\ge 0. $$
--
--   This is the monotonicity statement used when passing from the variational inequality at a solution to the contraction estimate. It does not require convexity of the objective or orthogonality of the matrices.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 5, after (2.5c)

import Definitions.Def_ExtADMM_Orth_Setting

set_option autoImplicit false

namespace ExtADMM.Orth

/-- The affine mapping F of (2.5c) is monotone (p. 5). -/
theorem F_monotone {n1 n2 n3 p : ℕ} (P : Problem n1 n2 n3 p)
    (a b : Pt n1 n2 n3 p) :
    0 ≤ pair (a - b) (P.F a - P.F b) := by sorry

end ExtADMM.Orth
