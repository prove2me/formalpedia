-- Prove2me | Theorems.Thm_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_flat_of_isIntegrallyClosed
-- name    : Algebra.isUnramifiedAt_of_forall_le_height_eq_one_of_flat_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/93e0c68b-34dc-5302-bcef-8b437871b79f
-- title:
--   Purity of the branch locus for finite flat extensions
-- statement:
--   Let $O$ be a Noetherian integrally closed domain with fraction field $K$, and let $C$ be an integrally closed domain with fraction field $F$ which is an $O$-algebra that is finite and flat as an $O$-module; the two fraction fields are tied together by an $O$-algebra structure on $F$ over $K$, compatible with the maps from $O$ and from $C$ (both towers $O \to K \to F$ and $O \to C \to F$ are scalar towers), and $F$ is assumed separable over $K$. Let $P$ be a prime ideal of $C$, and suppose that for every prime ideal $Q$ of $C$ with $Q \le P$ and $\operatorname{height} Q = 1$ the algebra $O \to C$ is unramified at $Q$, i.e. `Algebra.IsUnramifiedAt O Q` holds (the localisation $C_Q$ is formally unramified over $O$). Then $O \to C$ is unramified at $P$: `Algebra.IsUnramifiedAt O P`. All rings live in a single universe.
--
--   This is purity of the branch locus in the Auslander–Buchsbaum–Nagata form: over a normal Noetherian base, a module-finite flat extension of normal domains with separable fraction field extension is ramified only in codimension one, so being unramified at all height-one primes below $P$ forces being unramified at $P$. It is the flat (equivalently, locally free) version of the statement, which is what is available over a non-local normal base, and it is used in the construction of the modular curve $X_1$ to show that the relevant level-raising chart algebras are finite and étale.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_flat_of_isIntegrallyClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.isUnramifiedAt_of_forall_le_height_eq_one_of_flat_of_isIntegrallyClosed
    (O : Type u) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    (C : Type u) [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra O C] [Module.Finite O C] [Module.Flat O C]
    (F : Type u) [Field F] [Algebra C F] [IsFractionRing C F] [Algebra K F] [Algebra O F]
    [IsScalarTower O K F] [IsScalarTower O C F] [Algebra.IsSeparable K F]
    (P : Ideal C) [P.IsPrime]
    (h : ∀ (Q : Ideal C) [Q.IsPrime], Q ≤ P → Q.height = 1 → Algebra.IsUnramifiedAt O Q) :
    Algebra.IsUnramifiedAt O P := by sorry
