-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/7c51f9a8-5910-5895-855f-22d8b185e755
-- title:
--   Smoothness of a reduced irreducible component, tested on an affine chart
-- statement:
--   Let $s : X \to S$ be a morphism of schemes (in a fixed universe), let $Y$ be a closed subset of $X$ whose underlying set is an irreducible component of $X$, let $A$ be a commutative ring, let $g : \operatorname{Spec} A \to X$ be an open immersion, and let $n$ be a natural number. Assume that for every ideal $P$ of $A$ which is a minimal prime of $A$ and whose zero locus $V(P) \subseteq \operatorname{Spec} A$ equals the preimage $g^{-1}(Y)$ under the map of underlying spaces, the composite $\operatorname{Spec}(A/P) \to \operatorname{Spec} A \xrightarrow{g} X \xrightarrow{s} S$, formed from the map induced by the quotient $A \to A/P$ followed by $g$ followed by $s$, is smooth of relative dimension $n$. The conclusion is that the structure morphism to $S$ of the open subscheme of the closed subscheme cut out by the vanishing ideal sheaf of $Y$ lying over the open range of $g$ — namely the open immersion of the preimage of $g$'s range under the closed immersion $\operatorname{subscheme\iota}$, followed by that closed immersion and then by $s$ — is smooth of relative dimension $n$.
--
--   This is the local criterion that smoothness of the reduced induced structure on an irreducible component over the base can be checked on affine open charts, branch by branch over the minimal primes of the chart cutting out that component; the reducedness of the subscheme defined by a vanishing ideal sheaf enters as [`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`](thm.html#AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal). It is used in the Čerednik–Drinfel'd part of the development, in the construction of Mumford-type glueings, to exhibit irreducible components of a special fibre as integral closed subschemes that are smooth of relative dimension one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.IdealSheafData.smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion
    {X S : Scheme.{u}} (s : X ⟶ S) (Y : Closeds X) (hY : (Y : Set X) ∈ irreducibleComponents X)
    (A : Type u) [CommRing A] (g : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion g] (n : ℕ)
    (hP : ∀ P : Ideal A, P ∈ minimalPrimes A → PrimeSpectrum.zeroLocus (P : Set A) = g.base ⁻¹' (Y : Set X) →
      SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) ≫ g ≫ s)) :
    SmoothOfRelativeDimension n
      (((Scheme.IdealSheafData.vanishingIdeal Y).subschemeι ⁻¹ᵁ g.opensRange).ι ≫
        (Scheme.IdealSheafData.vanishingIdeal Y).subschemeι ≫ s) := by sorry
