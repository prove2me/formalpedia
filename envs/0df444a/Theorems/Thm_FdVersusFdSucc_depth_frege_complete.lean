-- Prove2me | Theorems.Thm_FdVersusFdSucc_depth_frege_complete
-- name    : FdVersusFdSucc.depth_frege_complete
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T10:13:19.426318+00:00
-- url     : https://prove2.me/theorems/e4cf4db7-ee51-490c-becf-ee1c0792cea1
-- title:
--   Completeness of $F_d$ for tautologies of depth at most $d$
-- statement:
--   Let $d\ge 0$ and let $A$ be a tautology with $\operatorname{depth}(A)\le d$. Then $A$ has an $F_d$-proof:
--   $$\operatorname{depth}(A)\le d,\ A \text{ tautology}\ \Longrightarrow\ \exists \pi,\ \pi \text{ is an } F_d\text{-proof of } A.$$
--
--   Together with soundness this shows that $F_d$ proves exactly the tautologies of depth at most $d$, so the question of the mission is purely about proof *size*.
-- source:
--   Standard (cut-free completeness of the sequent calculus with the subformula property); see J. Krajíček, Bounded arithmetic, propositional logic, and complexity theory, CUP 1995. Open Problem Garden, 'F_d versus F_{d+1}' (J. Krajíček), http://www.openproblemgarden.org/op/f_d_versus_f_d_1

import Definitions.Def_FdVersusFdSucc_defs

open Filter

namespace FdVersusFdSucc

/-- Completeness of `F_d` for depth-`d` formulas: every tautology of depth at most `d` has an
`F_d`-proof. -/
theorem depth_frege_complete (d : ℕ) (A : Formula) (hd : A.depth ≤ d)
    (hA : A.IsTautology) : ∃ π : List Sequent, IsDepthProofOf d π A := by sorry

end FdVersusFdSucc
