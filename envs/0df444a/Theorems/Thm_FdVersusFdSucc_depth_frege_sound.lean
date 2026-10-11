-- Prove2me | Theorems.Thm_FdVersusFdSucc_depth_frege_sound
-- name    : FdVersusFdSucc.depth_frege_sound
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:12:40.018976+00:00
-- url     : https://prove2.me/theorems/1675a988-8de8-404c-92f6-82e4b0c7729f
-- title:
--   Soundness of the depth-$d$ Frege system $F_d$
-- statement:
--   Let $d\ge 0$ and let $\pi$ be an $F_d$-proof of a formula $A$. Then $A$ is a tautology:
--   $$\pi \text{ is an } F_d\text{-proof of } A\ \Longrightarrow\ \forall v,\ v(A)=1.$$
--
--   This is the basic correctness property of the proof system $F_d$ and confirms that the lower and upper bounds in the mission are about a genuine propositional proof system.
-- source:
--   Standard property of bounded-depth Frege / sequent calculus systems; see J. Krajíček, Bounded arithmetic, propositional logic, and complexity theory, CUP 1995. Open Problem Garden, 'F_d versus F_{d+1}' (J. Krajíček), http://www.openproblemgarden.org/op/f_d_versus_f_d_1

import Definitions.Def_FdVersusFdSucc_defs

open Filter

namespace FdVersusFdSucc

/-- Soundness of `F_d`: every formula with an `F_d`-proof is a tautology. -/
theorem depth_frege_sound (d : ℕ) (π : List Sequent) (A : Formula)
    (h : IsDepthProofOf d π A) : A.IsTautology := by sorry

end FdVersusFdSucc
