-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot
-- name    : AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/2ede93aa-aca0-52f8-ae0f-1a57101c068b
-- title:
--   Factoring through a closed immersion descends along kerπ=bot
-- statement:
--   Let $T$, $T'$, $A$, $Z$ be schemes (in the bottom universe), let $\pi : T' \to T$ be a morphism of schemes whose scheme-theoretic kernel is trivial, that is, the quasi-coherent ideal sheaf $\pi.\mathrm{ker}$ on $T$ — the kernel of $\mathcal{O}_T \to \pi_*\mathcal{O}_{T'}$ — equals $\bot$, let $y : T \to A$ be a morphism, and let $\iota : Z \to A$ be a closed immersion. Assume that the composite $y \circ \pi : T' \to A$ factors through $\iota$, i.e. there exists $z' : T' \to Z$ with $\iota \circ z' = y \circ \pi$. Then $y$ itself factors through $\iota$: there exists $z : T \to Z$ with $\iota \circ z = y$. No compatibility between $z$ and $z'$ is asserted, and no uniqueness is asserted (although the factorisation is automatically unique, $\iota$ being a monomorphism).
--
--   This is the descent of the property 'factors through a given closed subscheme' along a morphism with injective unit map $\mathcal{O}_T \to \pi_*\mathcal{O}_{T'}$ (for instance along a faithfully flat, or a schematically dominant, morphism); the hypothesis $\pi.\mathrm{ker} = \bot$ is essential, since $\emptyset \to T$ would otherwise make the statement false. It is used in the construction of fake elliptic curves over Čerednik–Drinfel'd data, where it shows that a level structure recognised after base change along $\pi$ is already defined over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot
    {T T' A Z : Scheme.{0}} (π : T' ⟶ T) (hπ : π.ker = ⊥) (y : T ⟶ A) (ι : Z ⟶ A) [IsClosedImmersion ι]
    (h : ∃ z' : T' ⟶ Z, z' ≫ ι = π ≫ y) :
    ∃ z : T ⟶ Z, z ≫ ι = y := by sorry
