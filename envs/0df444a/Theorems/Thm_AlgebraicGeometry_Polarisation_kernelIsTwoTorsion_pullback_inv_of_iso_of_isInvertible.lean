-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_pullback_inv_of_iso_of_isInvertible
-- name    : AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_pullback_inv_of_iso_of_isInvertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/42091e8b-d5f8-50d1-91ea-a63604a77ac7
-- title:
--   Transport of the clause K(L)=A[2] along an isomorphism
-- statement:
--   Fix a commutative ring $S$ and two schemes $A$, $A'$ with morphisms $f : A \to \operatorname{Spec} S$ and $f' : A' \to \operatorname{Spec} S$, together with relative group laws $L$ on $f$ and $L'$ on $f'$, that is, functorial group structures on the sets $\{\varphi : T \to A \mid \varphi \circ \ldots = t\}$ of $T$-points over the base. Assume given an isomorphism of schemes $e : A \cong A'$ with $f' \circ e_{\mathrm{hom}} = f$ which is multiplicative on points: for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and all $T$-points $x,y$ of $A$ over $t$, the composite of $L.\mathrm{mul}\,t\,x\,y$ with $e_{\mathrm{hom}}$ equals $L'.\mathrm{mul}$ applied to the transported points $x \cdot e_{\mathrm{hom}}$ and $y \cdot e_{\mathrm{hom}}$. Let $\mathcal L$ be an object of `A.Modules` which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ with the restriction of $\mathcal L$ to $U$ isomorphic to the unit sheaf of modules, and assume `KernelIsTwoTorsion f L 𝓛`. The conclusion is `KernelIsTwoTorsion f' L' ((Scheme.Modules.pullback e.inv).obj 𝓛)`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every $R$-point $x$ of $A'$ over $t$, the pull-back along $\mathrm{sliceAt}\,f'\,x : A' \times_{\operatorname{Spec} S} \operatorname{Spec} R \to A' \times_{\operatorname{Spec} S} A'$ of the Mumford bundle $m^{*}\mathcal M \otimes \mathrm{pr}_1^{*}\mathcal M^{\vee} \otimes \mathrm{pr}_2^{*}\mathcal M^{\vee}$ of $\mathcal M = (e^{-1})^{*}\mathcal L$ is isomorphic to the unit object locally over $\operatorname{Spec} R$ — each point of $\operatorname{Spec} R$ has an open neighbourhood $U$ over whose preimage under the second projection the two modules become isomorphic — if and only if $L'.\mathrm{mul}\,t\,x\,x = L'.\mathrm{one}\,t$.
--
--   The condition `KernelIsTwoTorsion` expresses, in the language of Mumford bundles and points of the relative group law, that the kernel of the polarisation attached to $\mathcal L$ is exactly the $2$-torsion subgroup; this lemma transports that condition across an isomorphism of the ambient group schemes over $S$ that respects the group laws on points, the line bundle being carried along by pull-back under $e^{-1}$. It is used in the verification that the canonical polarisation data of the quaternionic Čerednik–Drinfeld setting is stable under such isomorphisms, via [`CerednikDrinfeld.QM.IsCanonicalPolData.pullback_inv_of_iso`](thm.html#CerednikDrinfeld.QM.IsCanonicalPolData.pullback_inv_of_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_pullback_inv_of_iso_of_isInvertible.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_pullback_inv_of_iso_of_isInvertible
    {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f')
    (e : A ≅ A') (he : e.hom ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f),
      (L.mul t x y).1 ≫ e.hom =
        (L'.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h : KernelIsTwoTorsion f L 𝓛) :
    KernelIsTwoTorsion f' L' ((Scheme.Modules.pullback e.inv).obj 𝓛) := by sorry
