-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_descent_and_iso_of_faithfullyFlat_of_three_le_of_rigidified
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_descent_and_iso_of_faithfullyFlat_of_three_le_of_rigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/07f2c4e2-9012-52b7-8ed4-e86de59061b8
-- title:
--   Effective faithfully flat descent for rigidified polarised abelian schemes
-- statement:
--   Fix natural numbers $g,d,n$ with $3\le n$, a commutative ring $S$ in which the image of $n$ is a unit, and a commutative $S$-algebra $S'$ that is faithfully flat as an $S$-module. Let $u'$ be a polarised abelian scheme of type $(g,d,n)$ over $S'$, i.e. a scheme $A'$ with a structure morphism to $\operatorname{Spec} S'$ carrying a commutative relative group law, smooth, proper, with connected fibres, all fibres of Krull dimension $g$, together with $2g$ sections $P_i$ over the identity base killed by $n$ which, on every geometric fibre, give an independent spanning family for the $n$-torsion, and an invertible module $\mathcal L'$ on $A'$ admitting a projective presentation whose associated map to $\mathbf{P}^N$ is a closed immersion and with geometric fibrewise $H^0$-dimension $d$. Assume (rigidification) that the pullback of $\mathcal L'$ along the unit section is isomorphic to the unit module on $\operatorname{Spec} S'$, and (descent datum) that any two polarised abelian schemes $v_1,v_2$ of type $(g,d,n)$ over $S'\otimes_S S'$ which are pullbacks of $u'$ along $\mathrm{includeLeft}$, respectively $\mathrm{includeRight}$, are isomorphic; here a pullback along a ring map is given by a morphism of total spaces forming a cartesian square over the induced map of spectra, compatible with multiplication and with the marked sections, and pulling $\mathcal L$ back to $\mathcal L'$, and an isomorphism is an isomorphism of schemes over the base respecting multiplication and the marked sections and matching the polarisations locally on the base. The conclusion has two parts: first, there is a polarised abelian scheme $u$ of type $(g,d,n)$ over $S$ such that every $v$ over $S'$ which is a pullback of $u$ along $S\to S'$ is isomorphic to $u'$ (existence of such a $v$ is not part of the assertion); second, if $u_1,u_2$ over $S$ have pullbacks $v_1,v_2$ along $S\to S'$ which are isomorphic, then $u_1$ and $u_2$ are isomorphic.
--
--   This is effectivity of faithfully flat descent for polarised abelian schemes with full level-$n$ structure, $n\ge3$ and invertible, in the rigidified case where the polarisation is trivial along the zero section, together with the accompanying separatedness (injectivity on isomorphism classes) statement. It feeds the level-$n$ descent statement for arbitrary base rings, the general case being reduced to the rigidified one by Zariski localisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_descent_and_iso_of_faithfullyFlat_of_three_le_of_rigidified.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_descent_and_iso_of_faithfullyFlat_of_three_le_of_rigidified
    {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
    (S' : Type) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (u' : PolarisedAbelianScheme g d n S')

    (hrig : Nonempty ((Scheme.Modules.pullback (u'.L.one (𝟙 _)).1).obj u'.pol ≅ SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf))
    (hdesc : ∀ (v₁ v₂ : PolarisedAbelianScheme g d n (S' ⊗[S] S')),
      PolarisedAbelianScheme.IsPullback
          (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom u' v₁ →
      PolarisedAbelianScheme.IsPullback
          (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom u' v₂ →
      PolarisedAbelianScheme.Iso v₁ v₂) :
    (∃ u : PolarisedAbelianScheme g d n S, ∀ v : PolarisedAbelianScheme g d n S',
        PolarisedAbelianScheme.IsPullback (algebraMap S S') u v → PolarisedAbelianScheme.Iso v u') ∧
    (∀ (u₁ u₂ : PolarisedAbelianScheme g d n S) (v₁ v₂ : PolarisedAbelianScheme g d n S'),
        PolarisedAbelianScheme.IsPullback (algebraMap S S') u₁ v₁ →
        PolarisedAbelianScheme.IsPullback (algebraMap S S') u₂ v₂ →
        PolarisedAbelianScheme.Iso v₁ v₂ → PolarisedAbelianScheme.Iso u₁ u₂) := by sorry
