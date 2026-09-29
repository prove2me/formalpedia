-- Prove2me | Theorems.Thm_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff
-- name    : ExtCitation.forall_exists_finiteDimensional_primeLocalToGlobal_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/36cb9b36-f432-5b88-b77b-00e45319c5d4
-- title:
--   Global and local smoothness agree for G_q-modules
-- statement:
--   Let $q$ be a prime, $k$ a commutative ring, and $M$ an object of `Rep k (primeLocalGaloisGroup q)`, that is a $k$-module with a $k$-linear action $\rho$ of the group $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$, realised in the project as the group of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl q` for the prime $q$. Here `primeLocalToGlobal q` is the monoid homomorphism from this local Galois group to $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ obtained by restricting scalars of an automorphism of `PadicAlgCl q` to $\mathbb{Q}$ and then restricting it to the normal subextension `AlgebraicClosure ℚ`. The assertion is an equivalence of two conditions on $M$. The first: for every $m \in M$ there is an intermediate field $F$ of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, finite-dimensional over $\mathbb{Q}$, such that every $s$ in the local Galois group whose image under `primeLocalToGlobal q` lies in the fixing subgroup of $F$ satisfies $\rho(s)m = m$. The second: for every $m \in M$ there is an intermediate field $K$ of $\mathbb{Q}_q \subseteq$ `PadicAlgCl q`, finite-dimensional over $\mathbb{Q}_q$, such that every $s$ in the fixing subgroup of $K$ satisfies $\rho(s)m = m$.
--
--   Both sides express that $M$ is a smooth (discrete) module for the local Galois group at $q$, the first in terms of finite subextensions of $\mathbb{Q}$ pulled back along the comparison map to the global Galois group, the second for the Krull topology on $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ itself. It serves to convert the smoothness hypothesis appearing in the local Euler-characteristic statements into its intrinsic local form, and is used by [`ExtCitation.exists_finiteDimensional_fixingSubgroup_comap_primeLocalToGlobal_le`](thm.html#ExtCitation.exists_finiteDimensional_fixingSubgroup_comap_primeLocalToGlobal_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff.lean

import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory ExtCitation

theorem ExtCitation.forall_exists_finiteDimensional_primeLocalToGlobal_iff
    (q : Nat.Primes) [Fact (q : ℕ).Prime]
    {k : Type} [CommRing k] (M : Rep k (primeLocalGaloisGroup q)) :
    (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m) ↔
      ∀ m : M, ∃ K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)), FiniteDimensional ℚ_[(q : ℕ)] K ∧
        ∀ s : primeLocalGaloisGroup q, s ∈ K.fixingSubgroup → M.ρ s m = m := by sorry
