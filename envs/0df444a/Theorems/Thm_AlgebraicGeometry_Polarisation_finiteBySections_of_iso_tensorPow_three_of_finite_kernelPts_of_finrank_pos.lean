-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_finiteBySections_of_iso_tensorPow_three_of_finite_kernelPts_of_finrank_pos
-- name    : AlgebraicGeometry.Polarisation.finiteBySections_of_iso_tensorPow_three_of_finite_kernelPts_of_finrank_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/4613ddf5-2ad1-5623-b4af-c2d692a7a42c
-- title:
--   Finiteness by sections of M^{⊗ 3} on an abelian variety
-- statement:
--   Let $k$ be an algebraically closed field (in the base universe), let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$, that is, a functorial group structure on the sets $\operatorname{Hom}_{\operatorname{Spec} k}(T, A)$ of $T$-points natural in $T \to \operatorname{Spec} k$; assume $L$ is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth and proper, that every fibre of $f$ on points of $\operatorname{Spec} k$ is connected, and that a relative group law on $f$ exists. Let $\mathcal M$ be a module over the structure sheaf of $A$ which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal M|_U$ isomorphic to the unit module on $U$. Assume that the set `kernelPts f L 𝓜` of $k$-points $x$ of $A$ lying in the stabiliser of $\mathcal M$ — those $x$ for which the pullback of $\mathcal M$ along translation by $x$ and the pullback of $\mathcal M$ along the first projection are locally isomorphic over the second projection of $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$ — is finite. Assume furthermore that $\Gamma(\mathcal M, \top)$, viewed as a $k$-vector space via the $k$-algebra structure on $\Gamma(A, \top)$ induced by $f$, has strictly positive finite rank. Finally let $\mathcal N$ be a module on $A$ with an isomorphism $\mathcal N \cong \mathcal M^{\otimes 3}$, the triple tensor power formed as $((\mathbf 1 \otimes \mathcal M) \otimes \mathcal M) \otimes \mathcal M$. Then $\mathcal N$ is finite by sections over $f$: there exist $N \in \mathbb N$ and a projective presentation of $\mathcal N$ consisting of global sections $\sigma_0, \dots, \sigma_N$ of $\mathcal N$ together with a morphism $\varphi : A \to \mathbb P^N_k$ over $\operatorname{Spec} k$ such that $\sigma_i$ frames $\mathcal N$ on every open contained in $\varphi^{-1}D_+(x_i)$ and the ratios $x_j/x_i$ act on $\sigma_i$ to give $\sigma_j$ there, and such that $\varphi$ is a finite morphism.
--
--   This is the instance $n = 3$ of the classical statement that for a non-degenerate invertible sheaf $\mathcal M$ with $h^0(\mathcal M) > 0$ on an abelian variety the cube $\mathcal M^{\otimes 3}$ defines a finite morphism to projective space, the first step towards projective embeddings of abelian varieties. It is used in the project's analysis of polarisations and symmetric line bundles, and in the construction of pullback squares for fake elliptic curves over discrete valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_finiteBySections_of_iso_tensorPow_three_of_finite_kernelPts_of_finrank_pos.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.finiteBySections_of_iso_tensorPow_three_of_finite_kernelPts_of_finrank_pos
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (hK : (kernelPts f L 𝓜).Finite)
    (hpos : letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓜, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
      0 < Module.finrank k Γ(𝓜, ⊤))
    (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓜.tensorPow 3) :
    𝓝.FiniteBySections f := by sorry
