-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_memKernel_tensor_tensor_iff_nsmul_six_eq_one_of_kernelIsTwoTorsion
-- name    : AlgebraicGeometry.Polarisation.memKernel_tensor_tensor_iff_nsmul_six_eq_one_of_kernelIsTwoTorsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/743cd6c5-70ce-57eb-b89b-13b4d9903cd9
-- title:
--   Kernel of L^{⊗ 3} is 6-torsion when K(L)=A[2]
-- statement:
--   Fix a commutative ring $S$ and a scheme $A$ (in universe $0$), a morphism $f : A \to \operatorname{Spec} S$, and a relative group law $L$ on $f$, i.e. functorial multiplication, unit and inverse operations on the sets $\mathrm{SchemeHomOver}\,t\,f$ of sections of $f$ over a base morphism $t$, satisfying the group axioms and compatible with base change. Assume: $L$ is commutative; $f$ carries the bundle of abelian-scheme properties (smooth, proper, with connected fibres over every point of $\operatorname{Spec} S$, and admitting a relative group law); $\mathcal L$ is a module on $A$ which is invertible, i.e. locally on $A$ its restriction is isomorphic to the structure sheaf; and $\mathcal L$ satisfies `KernelIsTwoTorsion`, namely for every test ring, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every section $x$ over $t$, the pullback along $\mathrm{sliceAt}\,f\,x$ of the Mumford bundle $m^*\mathcal L \otimes p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee$ on $A\times_S A$ is isomorphic to the unit module locally on the base if and only if $x \cdot x = e$. Then for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every section $y$ of $f$ over $t$, the point $y$ lies in the kernel of $\mathcal L \otimes \mathcal L \otimes \mathcal L$ (the same local-triviality condition for the Mumford bundle of $\mathcal L^{\otimes 3}$ sliced at $y$) if and only if the sixfold iterate $6 \cdot y$ equals the unit section over $t$.
--
--   This is the functor-of-points form of the identity $K(\mathcal L^{\otimes 3}) = A[6]$ for an invertible module whose theta group kernel is exactly $A[2]$, the case relevant to the canonical polarisation of an elliptic curve. It is used in the verification that such data give a polarised abelian scheme of type $(1,6,6)$, where the $6$-torsion description of the kernel is combined with the étale-local structure of $A[6]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_memKernel_tensor_tensor_iff_nsmul_six_eq_one_of_kernelIsTwoTorsion.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.Polarisation.memKernel_tensor_tensor_iff_nsmul_six_eq_one_of_kernelIsTwoTorsion
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : KernelIsTwoTorsion f L 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f) :
    MemKernel f L (𝓛 ⊗ 𝓛 ⊗ 𝓛) t y ↔ L.nsmul t 6 y = L.one t := by sorry
