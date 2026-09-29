-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_of_pullback_of_faithfullyFlat
-- name    : AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.of_pullback_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/b99bf57a-bbe5-557a-9a2f-4b7c5799188d
-- title:
--   K(L)=A[2] descends along faithfully flat base change
-- statement:
--   Let $S$ and $W$ be commutative rings with $W$ an $S$-algebra that is faithfully flat as an $S$-module, let $A$ and $A'$ be schemes, and let $f\colon A\to\operatorname{Spec}S$, $f'\colon A'\to\operatorname{Spec}W$ and $g\colon A'\to A$ be morphisms such that the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S\to W$ is cartesian. Assume given a relative group law $L$ for $f$ (a functorial group structure on the sets $\{\varphi\colon T\to A\mid \varphi\circ f = t\}$ of sections over varying $t\colon T\to\operatorname{Spec}S$, compatible with base change in $T$), the property bundle `AbelianSchemePropertyBundle` for $f$ (that is, $f$ is smooth and proper with connected fibres and admits some relative group law), and a relative group law $L'$ for $f'$ whose multiplication is carried to that of $L$ by $g$: for every scheme $T$, every $t'\colon T\to\operatorname{Spec}W$ and all sections $P,Q$ of $f'$ over $t'$, composing $L'.\mathrm{mul}\,t'\,P\,Q$ with $g$ equals the $L$-product over $t'$ followed by $\operatorname{Spec}(S\to W)$ of $P\circ g$ and $Q\circ g$. Let $\mathcal L$ be an $\mathcal O_A$-module which is invertible, i.e. locally on $A$ its restriction is isomorphic to the unit module. Then, if `KernelIsTwoTorsion` holds for $f'$, $L'$ and the pullback of $\mathcal L$ along $g$, it holds for $f$, $L$ and $\mathcal L$: for every commutative ring $R$, every $t\colon\operatorname{Spec}R\to\operatorname{Spec}S$ and every section $x$ of $f$ over $t$, the pullback along $\mathrm{sliceAt}\,f\,x$ of the Mumford bundle $m^*\mathcal L\otimes \mathrm{pr}_1^*\mathcal L^{\vee}\otimes \mathrm{pr}_2^*\mathcal L^{\vee}$ on $A\times_{\operatorname{Spec}S}A$ is isomorphic to the unit module over the preimage of some open neighbourhood of each point of $\operatorname{Spec}R$ (the relation `LocIsoOnBase` for $\mathrm{pr}_2\colon A\times_{\operatorname{Spec}S}\operatorname{Spec}R\to\operatorname{Spec}R$) if and only if $x\cdot x = e$ for $L$ over $t$.
--
--   This is the fpqc descent statement for the condition $K(\mathcal L)=A[2]$ on an invertible sheaf on an abelian scheme, expressed through the Mumford bundle $\Lambda(\mathcal L)$ and its slices at test points; it is the converse direction to the base-change compatibility of the same condition. It is used to transfer the property of being a suitable (principal) polarisation from a faithfully flat base extension back to the original base, for instance in the treatment of canonical polarisation data on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_of_pullback_of_faithfullyFlat.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.KernelIsTwoTorsion.of_pullback_of_faithfullyFlat
    {S W : Type u} [CommRing S] [CommRing W] [Algebra S W] [Module.FaithfullyFlat S W]
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of W)} {g : A' ⟶ A}
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f) (L' : RelativeGroupLaw W f')
    (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of W)) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S W)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : KernelIsTwoTorsion f' L' ((Scheme.Modules.pullback g).obj 𝓛)) :
    KernelIsTwoTorsion f L 𝓛 := by sorry
