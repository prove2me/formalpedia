-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_tensor_pullback_negMor_of_kernelTrivial_of_commRing
-- name    : AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_tensor_pullback_negMor_of_kernelTrivial_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/3a06880a-2744-586a-8986-98679f080aeb
-- title:
--   Mumford kernel of a symmetrised bundle is the 2-torsion
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f \colon A \to \operatorname{Spec} S$ a morphism, and $L$ a relative group law on $f$: a group structure, natural in the base, on the sets $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$ of sections over each $t \colon T \to \operatorname{Spec} S$. Assume $L$ is commutative; assume the bundle `AbelianSchemePropertyBundle` for $f$, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law on $f$ exists. Let $\mathcal L_0$ be a module on $A$ that is invertible, i.e. locally on $A$ its restriction is isomorphic to the unit sheaf, and assume `KernelTrivial` for $\mathcal L_0$: for every commutative ring $R$, every $t \colon \operatorname{Spec} R \to \operatorname{Spec} S$ and every section $x$ over $t$, if the pullback along $\mathrm{sliceAt}\, x$ of the Mumford bundle $\mathrm{addMor}^*\mathcal L_0 \otimes (\mathrm{pr}_1^*\mathcal L_0^\vee \otimes \mathrm{pr}_2^*\mathcal L_0^\vee)$ on $A \times_{\operatorname{Spec} S} A$ is isomorphic to the unit object after restriction over some open neighbourhood of each point of $\operatorname{Spec} R$ (the relation `LocIsoOnBase` for $\mathrm{pr}_2 \colon A \times_{\operatorname{Spec} S} \operatorname{Spec} R \to \operatorname{Spec} R$), then $x$ is the identity section. The conclusion is `KernelIsTwoTorsion` for $\mathcal L_0 \otimes N^*\mathcal L_0$, where $N = \mathrm{negMor}$ is the inversion morphism $A \to A$ obtained by inverting the identity section of $L$ over $f$: for every commutative ring $R$, every $t$ and every section $x$ over $t$, the slice at $x$ of the Mumford bundle of $\mathcal L_0 \otimes N^*\mathcal L_0$ is `LocIsoOnBase`-trivial over $\operatorname{Spec} R$ if and only if $x \cdot x$ is the identity section.
--
--   This is the computation $K(\mathcal L_0 \otimes [-1]^*\mathcal L_0) = A[2]$ for the Mumford kernel of the symmetrisation of a bundle with trivial kernel, here over an arbitrary commutative base ring and with triviality of the kernel read as local triviality of slices of the Mumford bundle on the base. It is used in the verification that a tensor product of this shape yields canonical polarisation data in the Čerednik–Drinfeld setting, and in the descent of the two-torsion kernel criterion along a faithfully flat base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_tensor_pullback_negMor_of_kernelTrivial_of_commRing.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_tensor_pullback_negMor_of_kernelTrivial_of_commRing
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (𝓛₀ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀) :
    KernelIsTwoTorsion f L (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀) := by sorry
