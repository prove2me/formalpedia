-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_iso_of_isPullback_pi_localizationAway_of_three_le
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_pi_localizationAway_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/73209d11-f327-5005-b789-15df4b3386b2
-- title:
--   Zariski descent of isomorphisms of polarised abelian schemes
-- statement:
--   Fix natural numbers $g,d,n$ with $3\le n$, a commutative ring $S$ in which the image of $n$ is a unit, and elements $r_1,\dots,r_k\in S$ ($r : \mathrm{Fin}\,k \to S$) generating the unit ideal, and assume the $S$-algebra $S_1 := \prod_{i} S[1/r_i]$ (the product of the localisations away from the $r_i$) is faithfully flat as an $S$-module. Let $u_1,u_2$ be objects of `PolarisedAbelianScheme g d n S` and $w_1,w_2$ objects of `PolarisedAbelianScheme g d n` $S_1$; such an object over a base ring consists of a scheme $A$ with a morphism $f : A \to \operatorname{Spec} S$ that is smooth, proper, with connected fibres and admitting a relative group law, a chosen commutative relative group law $L$ on the functor of sections of $f$, all fibres of $f$ of topological Krull dimension $g$, together with $2g$ sections $P_1,\dots,P_{2g}$ of $f$ over $\operatorname{Spec} S$ killed by $n$ under $L$ whose $\mathbb{Z}/n$-combinations are pairwise distinct and exhaust the $n$-torsion sections on every geometric fibre, and an invertible module `pol` on $A$ admitting a projective presentation over $f$ whose associated morphism to projective space is a closed immersion and whose $H^0$ on every geometric fibre has dimension $d$. Assume $w_1$, respectively $w_2$, is a base change of $u_1$, respectively $u_2$, along $\operatorname{Spec}$ of $S \to S_1$, in the sense that there is a morphism of total spaces making a cartesian square over $\operatorname{Spec}(S\to S_1)$, compatible with the group laws and the chosen sections, and pulling `pol` back to `pol` up to isomorphism. Then if $w_1$ and $w_2$ are isomorphic — an isomorphism of total spaces over $\operatorname{Spec} S_1$ compatible with the group laws and carrying the chosen sections to one another, under which the two polarising modules become isomorphic after restriction over some open neighbourhood of each point of the base — so are $u_1$ and $u_2$, in the same sense.
--
--   This is the descent (separatedness) statement for the moduli prestack of polarised abelian schemes with full level-$n$ structure, $n\ge 3$, along a finite cover by principal localisations: isomorphy of two objects is detected after base change to $\prod_i S[1/r_i]$. It is the Zariski case of the general faithfully flat descent statement [`AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le), and is used together with rigidity of level structures ([`AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le_of_locally`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le_of_locally)) and with [`AlgebraicGeometry.PolarisedAbelianScheme.iso_of_forall_isPullback_iso_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.iso_of_forall_isPullback_iso_of_three_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_iso_of_isPullback_pi_localizationAway_of_three_le.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_pi_localizationAway_of_three_le
    {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    [Module.FaithfullyFlat S (∀ i : Fin k, Localization.Away (r i))]
    (u₁ u₂ : PolarisedAbelianScheme g d n S) (w₁ w₂ : PolarisedAbelianScheme g d n (∀ i : Fin k, Localization.Away (r i)))
    (h₁ : PolarisedAbelianScheme.IsPullback (algebraMap S (∀ i : Fin k, Localization.Away (r i))) u₁ w₁)
    (h₂ : PolarisedAbelianScheme.IsPullback (algebraMap S (∀ i : Fin k, Localization.Away (r i))) u₂ w₂)
    (h : PolarisedAbelianScheme.Iso w₁ w₂) :
    PolarisedAbelianScheme.Iso u₁ u₂ := by sorry
