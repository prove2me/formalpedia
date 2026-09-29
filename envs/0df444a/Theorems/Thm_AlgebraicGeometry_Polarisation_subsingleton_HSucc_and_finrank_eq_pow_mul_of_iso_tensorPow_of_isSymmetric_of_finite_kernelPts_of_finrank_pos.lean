-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_HSucc_and_finrank_eq_pow_mul_of_iso_tensorPow_of_isSymmetric_of_finite_kernelPts_of_finrank_pos
-- name    : AlgebraicGeometry.Polarisation.subsingleton_HSucc_and_finrank_eq_pow_mul_of_iso_tensorPow_of_isSymmetric_of_finite_kernelPts_of_finrank_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/175958bd-4514-5186-832f-1c5ffffa4ffa
-- title:
--   Vanishing and h⁰(M^{⊗ n}) = n^g h⁰(M) for symmetric M
-- statement:
--   Let $k$ be an algebraically closed field, let $f \colon A \to \operatorname{Spec} k$ be a morphism of schemes (in universe $0$), and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$ of $T$-points over the base, compatible with base change; assume $L$ is commutative, and assume the bundle `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $g$ be a natural number with $f$ smooth of relative dimension $g$. Let $\mathcal M$ be an $\mathcal O_A$-module which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ on which the pullback of $\mathcal M$ to $U$ is isomorphic to the unit module; assume $\mathcal M$ is symmetric, i.e. the pullback of $\mathcal M$ along the inversion morphism attached to $L$ and $\mathcal M$ become isomorphic after pullback to $f^{-1}(U)$ for suitable open neighbourhoods $U$ of every point of the base; assume the set `kernelPts` of points over the identity of $\operatorname{Spec} k$ lying in the stabiliser of $\mathcal M$ for $L$ is finite; and assume that the space of global sections $\Gamma(\mathcal M, \top)$, viewed as a $k$-module through the $k$-algebra structure induced on $\Gamma(A, \top)$ by $f$, has positive finite rank. Finally let $n > 0$ and let $\mathcal N$ be an $\mathcal O_A$-module isomorphic to $\mathcal M^{\otimes n}$, the $n$-th tensor power formed by $\mathcal M^{\otimes 0} = \mathcal O_A$ and $\mathcal M^{\otimes (m+1)} = \mathcal M^{\otimes m} \otimes \mathcal M$. The conclusion is twofold: first, for every ordered affine cover $\mathcal U$ of $A$ (a finite linearly ordered family of affine opens with supremum $\top$) and every $i \in \mathbb{N}$, the group $\ker d_{i+1} / \operatorname{im} d_i$ of the complex attached to the $\mathcal O$-module presheaf of sections of $\mathcal N$ and to $\mathcal U$ is a subsingleton, i.e. all cohomology in degrees $\ge 1$ vanishes; second, $\operatorname{finrank}_k \Gamma(\mathcal N, \top) = n^g \cdot \operatorname{finrank}_k \Gamma(\mathcal M, \top)$.
--
--   This is the vanishing theorem together with the Riemann–Roch scaling $h^0(A, \mathcal M^{\otimes n}) = n^g h^0(A, \mathcal M)$ for a symmetric invertible sheaf with finite stabiliser and nonzero sections on an abelian variety of dimension $g$ over an algebraically closed field. It is used to produce enough sections of tensor powers of a canonical polarisation on the fake elliptic curves of the Čerednik–Drinfeld part of the development, where the resulting projective embeddings by sections of the third and fourth tensor power are constructed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_subsingleton_HSucc_and_finrank_eq_pow_mul_of_iso_tensorPow_of_isSymmetric_of_finite_kernelPts_of_finrank_pos.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
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

theorem AlgebraicGeometry.Polarisation.subsingleton_HSucc_and_finrank_eq_pow_mul_of_iso_tensorPow_of_isSymmetric_of_finite_kernelPts_of_finrank_pos
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (hsym : IsSymmetric f L 𝓜) (hK : (kernelPts f L 𝓜).Finite)
    (hpos : letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓜, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
      0 < Module.finrank k Γ(𝓜, ⊤))
    (n : ℕ) (hn : 0 < n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓜.tensorPow n) :
    letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module k Γ(𝓜, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
    letI : Module k Γ(𝓝, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
    (∀ (𝒰 : A.OrderedAffineCover) (i : ℕ), Subsingleton ((OModulePresheaf.ofModules f 𝓝).HSucc 𝒰 i)) ∧
      Module.finrank k Γ(𝓝, ⊤) = n ^ g * Module.finrank k Γ(𝓜, ⊤) := by sorry
