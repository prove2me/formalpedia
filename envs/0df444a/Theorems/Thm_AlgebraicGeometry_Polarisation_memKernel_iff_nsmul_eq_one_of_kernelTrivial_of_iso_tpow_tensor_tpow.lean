-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_memKernel_iff_nsmul_eq_one_of_kernelTrivial_of_iso_tpow_tensor_tpow
-- name    : AlgebraicGeometry.Polarisation.memKernel_iff_nsmul_eq_one_of_kernelTrivial_of_iso_tpow_tensor_tpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/fe0b94d2-b138-50e6-9224-e6e870346ebe
-- title:
--   Kernel of mathcal L₀ᵃ⊗([-1]^*mathcal L₀)ᵇ is the (a+b)-torsion
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism and $L$ a relative group law on $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over base changes $t : T \to \operatorname{Spec} S$; assume $L$ is commutative, and that $f$ is smooth, proper, with connected fibres and admitting a relative group law (the bundle `AbelianSchemePropertyBundle`). Let $\mathcal L_0$ be a module on $A$ that is invertible, i.e. locally on $A$ its restriction is isomorphic to the unit module, and assume $\mathcal L_0$ has trivial kernel in the sense of `KernelTrivial`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every section $x$ over $t$, if the pullback along the slice morphism $\operatorname{sliceAt} x : A\times_S \operatorname{Spec} R \to A \times_S A$ of the Mumford bundle $\Lambda(\mathcal L_0) = \mathrm{add}^*\mathcal L_0 \otimes (\mathrm{pr}_1^*\mathcal L_0^\vee \otimes \mathrm{pr}_2^*\mathcal L_0^\vee)$ is isomorphic to the unit module locally over the base $\operatorname{Spec} R$, then $x$ is the identity section. Let $a, b$ be natural numbers with $a + b \ge 1$ and let $\mathcal L$ be a module on $A$ together with an isomorphism $\mathcal L \cong \mathcal L_0^{\otimes a} \otimes \big(([-1])^*\mathcal L_0\big)^{\otimes b}$, where $[-1]$ is the inversion morphism $\operatorname{negMor} f L$ and the tensor powers are the iterated ones of `tpow`. Then for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every section $y$ over $t$: the pullback of $\Lambda(\mathcal L)$ along $\operatorname{sliceAt} y$ is locally over $\operatorname{Spec} R$ isomorphic to the unit module (membership in the kernel of $\mathcal L$) if and only if $(a+b)\cdot y$, formed by iterated multiplication in $L$, equals the identity section.
--
--   This is the computation of the theta group kernel $K(\mathcal L)$ for a bundle that is a formal $(a+b)$-th root datum built from a bundle $\mathcal L_0$ with trivial kernel: the kernel of such an $\mathcal L$ is exactly the $(a+b)$-torsion subgroup of the sections. It is used in the study of points of the theta/polarisation kernel on polarised abelian schemes, being cited in the proof that a suitable theta point is the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_memKernel_iff_nsmul_eq_one_of_kernelTrivial_of_iso_tpow_tensor_tpow.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.memKernel_iff_nsmul_eq_one_of_kernelTrivial_of_iso_tpow_tensor_tpow
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (hker : KernelTrivial f L 𝓛₀) (a b : ℕ) (hab : 1 ≤ a + b)
    (𝓛 : A.Modules)
    (e : 𝓛 ≅ Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (negMor f L)).obj 𝓛₀) b)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f) :
    MemKernel f L 𝓛 t y ↔ L.nsmul t (a + b) y = L.one t := by sorry
