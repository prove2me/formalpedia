-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_nonempty_iso_of_pullback_locally_iso_of_faithfullyFlat_of_rigidified
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.nonempty_iso_of_pullback_locally_iso_of_faithfullyFlat_of_rigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/1189a551-e44f-5e24-994e-06f20fe2bcc9
-- title:
--   Rigidified invertible modules isomorphic after faithfully flat base change
-- statement:
--   Fix natural numbers $g$, $d$, $n$ and commutative rings $S$, $S'$ with an $S$-algebra structure on $S'$ making $S'$ a faithfully flat $S$-module. Let $u$ be a polarised abelian scheme of the project's kind over $S$ and $v$ one over $S'$, with the same data $g,d,n$: each consists of a scheme with a structure morphism to the spectrum of the ring, a commutative relative group law on it, an `AbelianSchemePropertyBundle`, fibres of topological Krull dimension $g$, a family of $2g$ sections killed by $n$ which freely generate the $n$-torsion of every geometric fibre, and an invertible module that is very ample (a closed immersion by sections) with geometric fibre sections of rank $d$. Let $c : v.A \to u.A$ be a morphism making the square formed by $c$, $v.f$, $u.f$ and $\operatorname{Spec}$ of the structure map $S \to S'$ cartesian. Let $L$ and $M$ be modules on $u.A$, each invertible in the sense that every point has an open neighbourhood $U$ on which the restriction is isomorphic to the unit module, and suppose the pullbacks of $L$ and of $M$ along the zero section $e$ of the group law of $u$ (the underlying morphism of $u.L.one\ (\mathbb{1})$) are each isomorphic to the unit module on $\operatorname{Spec} S$. Suppose further that every point of $\operatorname{Spec} S'$ has an open neighbourhood $U$ such that the restrictions of $c^*L$ and $c^*M$ to the open subscheme $v.f^{-1}(U)$ of $v.A$ are isomorphic. Then $L$ and $M$ are isomorphic.
--
--   This is the rigidity-plus-descent step for line bundles on an abelian scheme: rigidification along the zero section turns an isomorphism of pullbacks, known only locally over the base after a faithfully flat base change, into a global isomorphism over the original base. It is used by [`AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le_of_rigidified`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le_of_rigidified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_nonempty_iso_of_pullback_locally_iso_of_faithfullyFlat_of_rigidified.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.nonempty_iso_of_pullback_locally_iso_of_faithfullyFlat_of_rigidified
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S') (c : v.A ⟶ u.A)
    (hc : CategoryTheory.IsPullback c v.f u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L M : u.A.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (hLe : Nonempty ((Scheme.Modules.pullback (u.L.one (𝟙 _)).1).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (hMe : Nonempty ((Scheme.Modules.pullback (u.L.one (𝟙 _)).1).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (hloc : ∀ s : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (v.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback c).obj L) ≅
        (Scheme.Modules.pullback (v.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback c).obj M))) :
    Nonempty (L ≅ M) := by sorry
