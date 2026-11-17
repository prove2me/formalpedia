-- Prove2me | Theorems.Thm_FLT_EDS_normEDS_conservation
-- name    : FLT.EDS.normEDS_conservation
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:29.157363+00:00
-- url     : https://prove2.me/theorems/9ac7f613-688f-4eb4-91ae-c291b78ab1c0
-- title:
--   The Ward numerator-to-denominator ratio is conserved
-- statement:
--   Let $R$ be a commutative ring, let $b,c,d∈R$, and put $u_n=normEDS(b,c,d;n)$. Define $N_n=u_{n+2}u_{n-1}^2+u_{n+1}^2u_{n-2}+b^2u_n^3$ and $D_n=u_{n+1}u_nu_{n-1}$. Then for every $n∈ℤ$, $$N_{n+1}D_n=N_nD_{n+1}.$$ Thus the formal ratio $N_n/D_n$ is independent of the index wherever division is valid, furnishing the conserved quantity used in the EDS argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_WardConservation
import Definitions.Def_WardSomos

open FLT
open FLT.EDS
variable {R : Type*} [CommRing R]

theorem FLT.EDS.normEDS_conservation (b c d : R) (n : ℤ) :
    Nseq b c d (n+1) * Dseq b c d n = Nseq b c d n * Dseq b c d (n+1) := by sorry
