-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_HSucc_and_finrank_eq_pow_mul_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos_u0
-- name    : AlgebraicGeometry.Polarisation.subsingleton_HSucc_and_finrank_eq_pow_mul_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos_u0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/7669c7c8-ffca-5e2a-9628-468a6c3f7bc4
-- title:
--   Vanishing and n^g-scaling of h⁰(M^{⊗ n})
-- statement:
--   Let $k$ be an algebraically closed field (a type in the lowest universe), let $A$ be a scheme and $f \colon A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$: a functorial group structure (multiplication, unit, inverse, associativity, unit laws, inverses, and compatibility with base change along maps $\psi$ over $\operatorname{Spec} k$) on the sets of $T$-points $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$, assumed commutative. Assume the bundle `AbelianSchemePropertyBundle` for $f$, i.e. $f$ is smooth, proper, has connected fibres and admits a relative group law, and assume $f$ is smooth of relative dimension $g$. Let $\mathcal M$ be an $A$-module that is invertible (every point has a neighbourhood $U$ on which the pullback along $U \hookrightarrow A$ is isomorphic to the unit module), such that the set `kernelPts f L 𝓜` — the sections $x$ of $f$ over $\operatorname{Spec} k$ satisfying `L.IsInStabilizer` for $\mathcal M$ — is finite, and such that $\Gamma(\mathcal M, \top)$ has positive finite rank over $k$, for the $k$-structure obtained from the $k$-algebra structure on $\Gamma(A, \top)$ induced by $f$. Finally let $n > 0$ and let $\mathcal N$ be an $A$-module with an isomorphism $\mathcal N \cong \mathcal M^{\otimes n}$, where the tensor power is defined recursively from the unit module. The conclusion is twofold: first, for every ordered affine cover $\mathcal U$ of $A$ (a finite linearly ordered family of affine opens with supremum $\top$) and every $i \in \mathbb N$, the module $\ker d^{i+1} / \operatorname{im} d^{i}$ of the alternating Čech complex of the presheaf of sections of $\mathcal N$ is a subsingleton; second, $\dim_k \Gamma(\mathcal N, \top) = n^{g} \cdot \dim_k \Gamma(\mathcal M, \top)$.
--
--   This is the combination, in the formalised Čech setting, of the vanishing theorem and the Riemann–Roch scaling $\chi(\mathcal M^{\otimes n}) = n^{g}\chi(\mathcal M)$ for a non-degenerate effective invertible sheaf on a $g$-dimensional abelian variety over an algebraically closed field. It is used downstream to compute the dimension of the space of global sections of tensor powers of a polarising line bundle, in particular in the treatment of framed polarised abelian schemes and of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_subsingleton_HSucc_and_finrank_eq_pow_mul_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos_u0.lean

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

theorem AlgebraicGeometry.Polarisation.subsingleton_HSucc_and_finrank_eq_pow_mul_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos_u0
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (hK : (kernelPts f L 𝓜).Finite)
    (hpos : letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓜, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
      0 < Module.finrank k Γ(𝓜, ⊤))
    (n : ℕ) (hn : 0 < n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓜.tensorPow n) :
    letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module k Γ(𝓜, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
    letI : Module k Γ(𝓝, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
    (∀ (𝒰 : A.OrderedAffineCover) (i : ℕ), Subsingleton ((OModulePresheaf.ofModules f 𝓝).HSucc 𝒰 i)) ∧
      Module.finrank k Γ(𝓝, ⊤) = n ^ g * Module.finrank k Γ(𝓜, ⊤) := by sorry
