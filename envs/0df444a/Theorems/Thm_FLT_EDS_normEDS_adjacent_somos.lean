-- Prove2me | Theorems.Thm_FLT_EDS_normEDS_adjacent_somos
-- name    : FLT.EDS.normEDS_adjacent_somos
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:31.897404+00:00
-- url     : https://prove2.me/theorems/800d99e9-9c85-48d7-8601-61694f865b02
-- title:
--   The normalized elliptic divisibility sequence satisfies the adjacent Somos relation
-- statement:
--   Let $R$ be a commutative ring, let $b,c,d∈R$, and write $u_n=normEDS(b,c,d;n)$ for the normalized elliptic divisibility sequence indexed by $n∈ℤ$. For every $m∈ℤ$, $$u_{m+2}u_{m-2}=b^2u_{m+1}u_{m-1}-cu_m^2.$$ This is the adjacent Somos recurrence underlying the Ward and Keystone certificate modules.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_WardSomos

open FLT
open FLT.EDS
variable {R : Type*} [CommRing R]

theorem FLT.EDS.normEDS_adjacent_somos (b c d : R) (m : ℤ) :
    normEDS b c d (m + 2) * normEDS b c d (m - 2)
      = b ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
          - c * normEDS b c d m ^ 2 := by sorry
