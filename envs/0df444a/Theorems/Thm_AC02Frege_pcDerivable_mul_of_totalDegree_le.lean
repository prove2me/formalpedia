-- Prove2me | Theorems.Thm_AC02Frege_pcDerivable_mul_of_totalDegree_le
-- name    : AC02Frege.pcDerivable_mul_of_totalDegree_le
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-11-17T06:03:19.385622+00:00
-- url     : https://prove2.me/theorems/88a5f5f3-057f-46b2-9762-2505e9005410
-- title:
--   Polynomial calculus is closed under polynomial multiplication within the degree budget
-- statement:
--   Let $F$ be a CNF on $n$ Boolean variables, and let polynomial calculus include its clause-complement polynomials and the Boolean axioms over $\mathbb F_2$. Suppose $u$ is derivable in formal degree at most $D$. For any formal polynomial $v$, if the sum of the total degrees of $u$ and $v$ is at most $D$, then
--   $$
--   u v\text{ is derivable in polynomial calculus in degree at most }D.
--   $$
--
--   This is the polynomial-multiplication step supporting Fact 2.5. It concerns the ordinary formal product before multilinearization; neither factor is required to be multilinear.
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds, November 3, 2026, https://www.doc.ic.ac.uk/~itzamere/Syntactic_ACZTwo.pdf, Definitions 2.1–2.4 and Fact 2.5, printed pp.9–10. Supporting lemma for the formalization of Fact 2.5; the source records degree-preserving multilinearization immediately before the fact.

import Definitions.Def_AC02Frege_PC
open MvPolynomial

theorem AC02Frege.pcDerivable_mul_of_totalDegree_le {n : ℕ}
    (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (u v : MvPolynomial (Fin n) (ZMod 2))
    (hu : AC02Frege.PCDerivable F D u)
    (hdeg : u.totalDegree + v.totalDegree ≤ D) :
    AC02Frege.PCDerivable F D (u * v) := by sorry
