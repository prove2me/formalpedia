-- Prove2me | Theorems.Thm_FLT_EDS_invarRel_all
-- name    : FLT.EDS.invarRel_all
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:31.7692+00:00
-- url     : https://prove2.me/theorems/ca5350e2-0d0e-42f1-ab06-e1aa7adb46dd
-- title:
--   The single-index Ward invariant holds at every integer
-- statement:
--   Let $R$ be an integral domain, let $b,c,d∈R$, and write $u_n=normEDS(b,c,d;n)$. Assume $u_k≠0$ for every nonzero $k∈ℤ$, and define $N_n=u_{n+2}u_{n-1}^2+u_{n+1}^2u_{n-2}+b^2u_n^3$ and $D_n=u_{n+1}u_nu_{n-1}$. Then every $n∈ℤ$ satisfies the Ward invariant $$cN_n=(d+b^4)D_n.$$ This gives the index-independent invariant needed to derive the full elliptic-divisibility relations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_WardConservation
import Definitions.Def_WardInvariant

open FLT
open FLT.EDS
variable {R : Type*} [CommRing R]

theorem FLT.EDS.invarRel_all [IsDomain R] (b c d : R)
    (hne : ∀ k : ℤ, k ≠ 0 → normEDS b c d k ≠ 0) (n : ℤ) : InvarRel b c d n := by sorry
