-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_pos_of_iso_tensorPow_tensor_of_inPicZero_of_kernelPts_finite
-- name    : AlgebraicGeometry.Polarisation.geomFibreH0Finrank_pos_of_iso_tensorPow_tensor_of_inPicZero_of_kernelPts_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c4fe23db-a0a7-5a1e-ada0-6f4474babecf
-- title:
--   Effectivity descends from M^{⊗ n}⊗ P to M
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, equipped with a relative group law $L$ (a group structure on the sets of $T$-points of $f$ over $\operatorname{Spec} k$, natural in $T$) which is commutative, and with `AbelianSchemePropertyBundle` data for $f$: $f$ is smooth, proper, each fibre $f^{-1}(s)$ is connected, and $f$ carries a relative group law. Let $g$ be a natural number such that every fibre of $f$ has topological Krull dimension $g$. Let $\mathcal M$ be an $\mathcal O_A$-module that is invertible (every point has a neighbourhood $U$ on which the restriction of $\mathcal M$ is isomorphic to the unit module) and assume the set `kernelPts` $f$ $L$ $\mathcal M$ of sections $x : \operatorname{Spec} k \to A$ of $f$ lying in the stabiliser of $\mathcal M$ (translation by $x$ pulls $\mathcal M$ back to a module locally isomorphic to $\mathcal M$ over the base) is finite. Let $n > 0$, let $P$ be an $\mathcal O_A$-module lying in $\operatorname{Pic}^0$ in the sense of `InPicZero`, i.e. $P$ is invertible and all translates $T_x^{*}P$ are isomorphic to $P$, and let $\mathcal N$ be isomorphic to $\mathcal M^{\otimes n} \otimes P$, where $\mathcal M^{\otimes n}$ is the iterated tensor power built from the unit module. Assume that for every algebraically closed field $k'$ and every ring homomorphism $k \to k'$ the quantity `Scheme.Modules.geomFibreH0Finrank` of $\mathcal N$ — the $k'$-dimension of the global sections of the base change of $\mathcal N$ along $\operatorname{Spec} k' \to \operatorname{Spec} k$ — is positive. Then, for a given algebraically closed field $k'$ and ring homomorphism $sk : k \to k'$, the same invariant for $\mathcal M$ is positive.
--
--   This is the index-zero case of the invariance of the index of a non-degenerate line bundle on an abelian variety under passage to positive tensor powers and twists by algebraically trivial bundles: effectivity of $\mathcal M^{\otimes n}\otimes P$ over all algebraically closed extensions forces effectivity of $\mathcal M$. It is used in the construction of canonical polarisations on fake elliptic curves in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_pos_of_iso_tensorPow_tensor_of_inPicZero_of_kernelPts_finite.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.geomFibreH0Finrank_pos_of_iso_tensorPow_tensor_of_inPicZero_of_kernelPts_finite
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (hK : (kernelPts f L 𝓜).Finite)
    (n : ℕ) (hn : 0 < n) (P : A.Modules) (hP : InPicZero f L P)
    (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓜.tensorPow n ⊗ P)
    (hpos : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank f 𝓝 k' sk)
    (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') :
    0 < Scheme.Modules.geomFibreH0Finrank f 𝓜 k' sk := by sorry
