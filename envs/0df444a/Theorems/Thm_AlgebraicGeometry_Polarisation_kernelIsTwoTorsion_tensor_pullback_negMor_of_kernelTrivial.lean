-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_tensor_pullback_negMor_of_kernelTrivial
-- name    : AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_tensor_pullback_negMor_of_kernelTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/b62833d0-b7ea-55a3-9fe1-1d5f881c8d97
-- title:
--   Symmetrisation of a sheaf with trivial kernel has kernel A[2]
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$, equipped with a relative group law $L$ on $f$ (functorial multiplication, unit and inverse on the sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $f$ over each $k$-scheme $t : T \to \operatorname{Spec} k$, satisfying associativity, the unit laws, left inversion, and naturality of multiplication under base change), assumed commutative, and let $hA$ assert that $f$ is smooth and proper with connected fibres and admits a relative group law. Let $\mathcal L_0$ be a module on $A$ that is invertible, in the sense that every point of $A$ has an open neighbourhood on which the restriction of $\mathcal L_0$ is isomorphic to the unit sheaf of modules. Assume `KernelTrivial f L 𝓛₀`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every section $x$ of $f$ over $t$, if the pullback along the slice morphism $\mathrm{sliceAt}\,x : A \times_{\operatorname{Spec} k} \operatorname{Spec} R \to A \times_{\operatorname{Spec} k} A$ of the Mumford bundle $\Lambda(\mathcal L_0) = m^*\mathcal L_0 \otimes (\mathrm{pr}_1^*\mathcal L_0^\vee \otimes \mathrm{pr}_2^*\mathcal L_0^\vee)$ is, locally on the base $\operatorname{Spec} R$ (i.e. after restriction to the preimage of some open neighbourhood of each point of $\operatorname{Spec} R$ under the second projection), isomorphic to the unit module, then $x$ is the unit section. The conclusion is `KernelIsTwoTorsion` for $\mathcal L := \mathcal L_0 \otimes [-1]^*\mathcal L_0$, where $[-1] =$ `negMor f L` is the underlying morphism $A \to A$ of the $L$-inverse of the identity section: for all such $R$, $t$ and $x$, the slice of $\Lambda(\mathcal L)$ at $x$ is locally on the base isomorphic to the unit module if and only if $x \cdot x$ equals the unit section over $t$.
--
--   This is Mumford's computation that the symmetrisation $\mathcal L_0 \otimes [-1]^*\mathcal L_0$ of an invertible sheaf whose theta group kernel is trivial has kernel exactly the $2$-torsion subscheme, here in the form of a statement about $R$-points for arbitrary test rings $R$. It feeds the construction of canonical polarisation data on the quaternionic Shimura curve side and the comparison of kernels along a pullback square.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_tensor_pullback_negMor_of_kernelTrivial.lean

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

theorem AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_tensor_pullback_negMor_of_kernelTrivial
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀) :
    KernelIsTwoTorsion f L (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀) := by sorry
