-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_not_forall_nonempty_pullback_translate_tensor_iso_of_kernelTrivial_of_geomFibreH0Finrank_pos
-- name    : AlgebraicGeometry.Polarisation.not_forall_nonempty_pullback_translate_tensor_iso_of_kernelTrivial_of_geomFibreH0Finrank_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/818eab26-e653-5ac8-ae65-edb4d510ceb5
-- title:
--   Two effective bundles with K(mathcal L₀) trivial are never in Pic⁰
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism equipped with a relative group law $L$ (a functorial, associative, unital group structure, natural in the test scheme, on the sets of morphisms into $A$ over a given morphism to $\operatorname{Spec} k$), assumed commutative, and assume $f$ satisfies the bundle of properties that it is smooth, proper, has connected fibres and admits a relative group law. Suppose every fibre $f^{-1}(s)$ has topological Krull dimension $g$ with $1 \le g$. Let $\mathcal L_0, \mathcal L_1$ be modules on $A$ which are invertible, in the sense that each point has an open neighbourhood $U$ on which the restriction is isomorphic to the unit module, and assume: $\mathcal L_0$ has trivial kernel, i.e. for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every point $x$ of $A$ over $t$, if the pullback along the slice $\mathrm{sliceAt}\ f\ x$ of the Mumford bundle $m^*\mathcal L_0 \otimes p_1^*\mathcal L_0^\vee \otimes p_2^*\mathcal L_0^\vee$ is locally isomorphic, over the base $\operatorname{Spec} R$, to the unit module, then $x$ is the identity section over $t$; and both $\mathcal L_0$ and $\mathcal L_1$ have positive $k$-dimension of global sections after base change along the identity of $k$. Then it is false that for every $k$-point $x$ of $A$ the pullback of $\mathcal L_1 \otimes \mathcal L_0$ along the translation by $x$ is isomorphic to $\mathcal L_1 \otimes \mathcal L_0$.
--
--   This is the step by which positivity fixes the sign in the uniqueness of a principal polarisation: two invertible sheaves with non-vanishing $H^0$, one of them with trivial kernel, cannot have translation-invariant tensor product, i.e. cannot have product in $\operatorname{Pic}^0(A)$. It is used in the Čerednik–Drinfel'd fake elliptic curve material, where it rules out the possibility that the polarisation attached to $\mathcal L_1$ is the negative of the one attached to $\mathcal L_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_not_forall_nonempty_pullback_translate_tensor_iso_of_kernelTrivial_of_geomFibreH0Finrank_pos.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.not_forall_nonempty_pullback_translate_tensor_iso_of_kernelTrivial_of_geomFibreH0Finrank_pos
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g) (hg : 1 ≤ g)
    (𝓛₀ 𝓛₁ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) (h₁ : Scheme.Modules.IsInvertible 𝓛₁)
    (hK₀ : KernelTrivial f L 𝓛₀)
    (hpos₀ : 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛₀ k (RingHom.id k))
    (hpos₁ : 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛₁ k (RingHom.id k)) :
    ¬ ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
        Nonempty ((Scheme.Modules.pullback (L.translate x)).obj (𝓛₁ ⊗ 𝓛₀) ≅ 𝓛₁ ⊗ 𝓛₀) := by sorry
