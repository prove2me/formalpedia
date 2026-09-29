-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_HSucc_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos
-- name    : AlgebraicGeometry.Polarisation.subsingleton_HSucc_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/14fed058-438b-5ce6-84d2-00c9adb0b406
-- title:
--   Čech vanishing for powers of an effective nondegenerate line bundle
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme with a morphism $f : A \to \operatorname{Spec} k$, and let $L$ be a `RelativeGroupLaw` for $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t : T \to \operatorname{Spec} k$, natural in $T$; assume $L$ is commutative, and that the bundle `AbelianSchemePropertyBundle` holds for $f$, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal M$ be an object of `A.Modules` which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal M|_U$ isomorphic to the unit module on $U$. Assume the set `kernelPts f L 𝓜` of sections $x$ of $f$ over $\operatorname{Spec} k$ satisfying the stabiliser predicate `L.IsInStabilizer` for $\mathcal M$ is finite, and that the space of global sections $\Gamma(\mathcal M, \top)$, viewed as a $k$-module through the $k$-algebra structure on $\Gamma(A, \top)$ induced by $f$, has positive finite rank. Let $n > 0$, let $\mathcal N$ be an object of `A.Modules` isomorphic to $\mathcal M^{\otimes n}$ (the $n$-fold tensor power formed by $\mathcal M^{\otimes 0} = \mathbf 1$ and $\mathcal M^{\otimes (m+1)} = \mathcal M^{\otimes m} \otimes \mathcal M$), let $\mathcal U$ be an ordered affine cover of $A$ (a finite linearly ordered family of affine opens with supremum $\top$), and let $i$ be a natural number. Then the degree-$(i+1)$ cohomology `HSucc` of the complex attached to $\mathcal U$ and the presheaf of modules $U \mapsto \Gamma(\mathcal N, U)$, namely the quotient of $\ker d^{i+1}$ by the part of $\operatorname{im} d^{i}$ lying in it, is a subsingleton.
--
--   This is the vanishing theorem on an abelian variety: for an invertible sheaf with finite stabiliser group of $k$-points and a non-zero global section, all positive-degree cohomology of $\mathcal M^{\otimes n}$, $n \ge 1$, vanishes, here in the form of alternating Čech cohomology for an arbitrary ordered affine cover and for any module isomorphic to the $n$-th power. It feeds the computation of $h^0$ of powers of a polarisation and the construction of closed immersions by global sections, and thence the geometric-fibre positivity statements used for Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_subsingleton_HSucc_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.subsingleton_HSucc_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (hK : (kernelPts f L 𝓜).Finite)
    (hpos : letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓜, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
      0 < Module.finrank k Γ(𝓜, ⊤))
    (n : ℕ) (hn : 0 < n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓜.tensorPow n)
    (𝒰 : A.OrderedAffineCover) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules f 𝓝).HSucc 𝒰 i) := by sorry
