-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_of_kernelTrivial_pullback_of_isPullback_of_field
-- name    : AlgebraicGeometry.Polarisation.kernelTrivial_of_kernelTrivial_pullback_of_isPullback_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/caa48b0d-8ad2-5082-8e32-58e136942189
-- title:
--   Triviality of K(L) descends along a field extension
-- statement:
--   Let $k \subseteq k'$ be fields with $k'$ a $k$-algebra, and let $f : A \to \operatorname{Spec} k$ and $f' : A' \to \operatorname{Spec} k'$ be morphisms of schemes equipped with relative group laws $L$, $L'$, that is, functorial group structures on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over a variable base morphism $t$. Let $g : A' \to A$ be a morphism making the square with $f'$, $f$ and $\operatorname{Spec}$ of $k \to k'$ cartesian, and assume $g$ is multiplicative in the strong sense that for every scheme $T$, every $t' : T \to \operatorname{Spec} k'$ and all sections $P, Q$ of $f'$ over $t'$, the underlying morphism of $L'.\mathrm{mul}\,t'\,P\,Q$ followed by $g$ equals the underlying morphism of the $L$-product, over $t'$ followed by $\operatorname{Spec}(k \to k')$, of the images of $P$ and $Q$ under composition with $g$. Let $\mathcal L$ be a module on $A$ that is invertible, in the sense that each point of $A$ has an open neighbourhood on which the restriction of $\mathcal L$ is isomorphic to the unit module. Suppose $g^{*}\mathcal L$ has trivial kernel for $(f', L')$, i.e. for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k'$ and every section $x$ of $f'$ over $t$: if the pullback along the slice morphism $\operatorname{Spec} R \times_{\operatorname{Spec} k'} A' \to A' \times_{\operatorname{Spec} k'} A'$ determined by $x$ of the Mumford bundle $m^{*}g^{*}\mathcal L \otimes (p_1^{*}(g^{*}\mathcal L)^{\vee} \otimes p_2^{*}(g^{*}\mathcal L)^{\vee})$ is, locally over each point of $\operatorname{Spec} R$, isomorphic to the unit module, then $x$ is the identity section. The conclusion is the same statement for $f$, $L$ and $\mathcal L$ over $k$.
--
--   Classically this is the descent, along a base field extension, of the assertion that the kernel $K(\mathcal L)$ of the polarisation attached to a line bundle $\mathcal L$ on an abelian variety is trivial, i.e. that $\mathcal L$ is nondegenerate with trivial kernel; here the kernel is expressed functorially through the triviality of slices of the Mumford bundle $\Lambda(\mathcal L) = m^{*}\mathcal L \otimes p_1^{*}\mathcal L^{\vee} \otimes p_2^{*}\mathcal L^{\vee}$. It is used to transfer triviality of the kernel from a geometric or algebraically closed base back to the original field, in the construction of polarised abelian schemes with prescribed Euler characteristic and in the Čerednik–Drinfeld treatment of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelTrivial_of_kernelTrivial_pullback_of_isPullback_of_field.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.kernelTrivial_of_kernelTrivial_pullback_of_isPullback_of_field
    (k k' : Type) [Field k] [Field k'] [Algebra k k']
    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (f' : A' ⟶ Spec (CommRingCat.of k')) (L' : RelativeGroupLaw k' f')
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : KernelTrivial f' L' ((Scheme.Modules.pullback g).obj 𝓛)) :
    KernelTrivial f L 𝓛 := by sorry
