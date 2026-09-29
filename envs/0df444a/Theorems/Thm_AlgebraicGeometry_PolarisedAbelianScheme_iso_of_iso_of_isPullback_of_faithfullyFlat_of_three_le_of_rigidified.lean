-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le_of_rigidified
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le_of_rigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/97ecb191-9814-5151-973f-564b92d32a68
-- title:
--   Flat descent of isomorphisms of rigidified polarised abelian schemes
-- statement:
--   Fix natural numbers $g, d, n$ with $3 \le n$, a commutative ring $S$ in which the image of $n$ is a unit, and an $S$-algebra $S'$ that is faithfully flat as an $S$-module. Let $u_1, u_2$ be objects of `PolarisedAbelianScheme g d n S`: each consists of a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} S$ carrying a commutative relative group law $L$ on $T$-points together with the smooth, proper, connected-fibre bundle `AbelianSchemePropertyBundle`, all fibres of $f$ of topological Krull dimension $g$, sections $P_0,\dots,P_{2g-1}$ of $f$ killed by $n$ which on every geometric fibre are independent and generate the $n$-torsion, and an invertible module `pol` on $A$ which is a closed immersion by sections over $\operatorname{Spec} S$ and whose geometric fibre $H^0$ has rank $d$. Assume each `pol` is rigidified, i.e. its pullback along the unit section $L.one(\mathrm{id})$ is isomorphic to the unit sheaf of modules on $\operatorname{Spec} S$. Let $v_1, v_2$ be objects over $S'$ together with `IsPullback` data for $\operatorname{algebraMap} S\ S'$: morphisms $v_i.A \to u_i.A$ cartesian over $\operatorname{Spec} S' \to \operatorname{Spec} S$, compatible with the group laws on points and with the level sections, and identifying the pullback of $u_i.\mathrm{pol}$ with $v_i.\mathrm{pol}$. If $v_1$ and $v_2$ are isomorphic in the sense of `PolarisedAbelianScheme.Iso` — an isomorphism of schemes over the base respecting the group law and the level sections and matching the polarisations locally on the base — then $u_1$ and $u_2$ are isomorphic in that same sense.
--
--   This is the rigidified form of the descent (separatedness) statement for the prestack of polarised abelian schemes with full level-$n$ structure, $n \ge 3$ invertible: isomorphisms may be recovered after a faithfully flat base change. It is the core used by [`AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le), which removes the rigidification hypotheses by localising the base so that the polarisations become trivial along the zero sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le_of_rigidified.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le_of_rigidified
    {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
    (S' : Type) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (u₁ u₂ : PolarisedAbelianScheme g d n S)

    (hrig₁ : Nonempty ((Scheme.Modules.pullback (u₁.L.one (𝟙 _)).1).obj u₁.pol ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (hrig₂ : Nonempty ((Scheme.Modules.pullback (u₂.L.one (𝟙 _)).1).obj u₂.pol ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (v₁ v₂ : PolarisedAbelianScheme g d n S')
    (h₁ : PolarisedAbelianScheme.IsPullback (algebraMap S S') u₁ v₁)
    (h₂ : PolarisedAbelianScheme.IsPullback (algebraMap S S') u₂ v₂)
    (h : PolarisedAbelianScheme.Iso v₁ v₂) :
    PolarisedAbelianScheme.Iso u₁ u₂ := by sorry
