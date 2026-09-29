-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_finrank_sections_pos_of_iso_tensor_self_of_kernelTrivial_of_isSymmetric
-- name    : AlgebraicGeometry.Polarisation.finrank_sections_pos_of_iso_tensor_self_of_kernelTrivial_of_isSymmetric
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c8a7966c-b46c-529c-b165-e6a5e4a2d2ee
-- title:
--   Effectivity of mathcal L₀ from that of mathcal L₀^{⊗ 2}
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, equipped with a relative group law $L$ on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-points over arbitrary $t : T \to \operatorname{Spec} k$, compatible with base change) which is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle`: $f$ is smooth and proper, each fibre of $f$ is connected, and $f$ carries a relative group law. Let $g$ be a natural number with $f$ smooth of relative dimension $g$. Let $\mathcal L_0$ be a module over $A$ which is invertible, i.e. every point of $A$ has an open neighbourhood $U$ with the restriction of $\mathcal L_0$ to $U$ isomorphic to the unit module. Assume `KernelTrivial f L 𝓛₀`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every $A$-point $x$ over $t$, if the pullback along `sliceAt f x` of the Mumford bundle $m^*\mathcal L_0 \otimes p_1^*\mathcal L_0^{\vee} \otimes p_2^*\mathcal L_0^{\vee}$ on $A \times A$ is, locally on $\operatorname{Spec} R$, isomorphic to the unit module, then $x$ is the identity point $L.\mathrm{one}\,t$. Assume also that $\mathcal L_0$ is symmetric, i.e. the pullback of $\mathcal L_0$ along the inversion morphism of $L$ is, locally on the base, isomorphic to $\mathcal L_0$. Finally let $\mathcal N$ be a module over $A$ with an isomorphism $\mathcal N \cong \mathcal L_0 \otimes \mathcal L_0$, and suppose $\Gamma(\mathcal N, \top)$ has positive finite rank as a $k$-module, the $k$-structure coming from the $k$-algebra structure on $\Gamma(A, \top)$ induced by $f$. Then $\Gamma(\mathcal L_0, \top)$ likewise has positive $k$-rank.
--
--   This is the step, for an abelian variety over an algebraically closed field with a symmetric line bundle of trivial kernel, that descends effectivity from $\mathcal L_0^{\otimes 2}$ to $\mathcal L_0$ itself, i.e. $h^0(\mathcal L_0^{\otimes 2}) > 0 \Rightarrow h^0(\mathcal L_0) > 0$. It is used in the construction of canonical polarisation data on the quaternionic Shimura curves side, where a line bundle with trivial kernel and a non-zero section of its square is produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_finrank_sections_pos_of_iso_tensor_self_of_kernelTrivial_of_isSymmetric.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.finrank_sections_pos_of_iso_tensor_self_of_kernelTrivial_of_isSymmetric
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝓛₀ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀) (hsym : IsSymmetric f L 𝓛₀)
    (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓛₀ ⊗ 𝓛₀)
    (hpos : letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓝, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
      0 < Module.finrank k Γ(𝓝, ⊤)) :
    letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module k Γ(𝓛₀, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
    0 < Module.finrank k Γ(𝓛₀, ⊤) := by sorry
