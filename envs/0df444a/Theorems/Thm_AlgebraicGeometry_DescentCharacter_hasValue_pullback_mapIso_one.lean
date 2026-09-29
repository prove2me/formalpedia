-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_pullback_mapIso_one
-- name    : AlgebraicGeometry.DescentCharacter.hasValue_pullback_mapIso_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/42fd4f84-25bb-5e70-bf5e-61849f1860b1
-- title:
--   Pulled-back isomorphisms have descent value one
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe), let $R$ be a commutative ring, and let $f : X \to \operatorname{Spec}(R)$ be a morphism of schemes to the spectrum of $R$. Let $T : X \to X$ and $q : X \to Y$ be morphisms with $T$ followed by $q$ equal to $q$, this equality being the hypothesis $h$. Let $N$ and $M$ be objects of `Y.Modules` and let $\iota : N \cong M$ be an isomorphism between them. The assertion is that the pulled-back isomorphism $(\text{Scheme.Modules.pullback } q).mapIso\ \iota$, an isomorphism from $q^{*}N$ to $q^{*}M$, satisfies `HasValue f h … 1`, i.e. its discrepancy at $T$ — the composite of the inverse of the isomorphism with its $T$-translate `translateIso h`, an automorphism of $q^{*}M$ — is the base scalar $1$: for every open subset $U$ of $X$ and every section $s$ of $q^{*}M$ over $U$, the component at $U$ of the forward map of this discrepancy sends $s$ to $\mathrm{baseSection}\, f\, 1\, U \cdot s$.
--
--   In descent language this records that an isomorphism coming from the base is a morphism of descent data, so that its descent character at any endomorphism $T$ over $q$ is trivial; in the guiding case $q = [n]$ on an abelian scheme and $T$ translation by an $n$-torsion point, it is the normalisation underlying the values of the Weil pairing. It is used in the construction of rigidified line bundles and torsion characters attached to a polarisation, notably by [`AlgebraicGeometry.Polarisation.torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate`](thm.html#AlgebraicGeometry.Polarisation.torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate) and the two existence statements for trivialisations of pullbacks along multiplication by two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentCharacter_hasValue_pullback_mapIso_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.hasValue_pullback_mapIso_one
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules} (ι : N ≅ M) :
    HasValue f h ((Scheme.Modules.pullback q).mapIso ι) 1 := by sorry
