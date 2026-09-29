-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit
-- name    : AlgebraicGeometry.OModulePresheaf.isCoherent_isQuasicoherent_supportedIn_pushforwardUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/60aa3042-86fc-58e0-a6de-076c6146ed4d
-- title:
--   Push-forward of 𝒪_Z along a closed immersion: coherence and support
-- statement:
--   Let $R$ be a commutative ring, let $V$ and $Z$ be schemes, let $\pi : V \to \operatorname{Spec} R$ be a morphism and let $\iota : Z \to V$ be a closed immersion. Consider the presheaf-of-modules datum `pushforwardUnit` $\pi$ $\iota$, which assigns to an open $U \subseteq V$ the ring $\Gamma(Z, \iota^{-1}U)$, regarded as a module over $R$ and over $\Gamma(V, U)$ through the ring map $\Gamma(V,U) \to \Gamma(Z, \iota^{-1}U)$ induced by $\iota$, with restriction maps those of $\mathcal{O}_Z$ along preimages. The assertion is the conjunction of three statements. First, coherence in the affine-local sense: for every affine open $U$ of $V$, $\Gamma(Z, \iota^{-1}U)$ is a finite $\Gamma(V,U)$-module. Second, quasi-coherence in the affine-local sense: for every affine open $U$ of $V$ and every $f \in \Gamma(V,U)$, each $x \in \Gamma(Z, \iota^{-1}D(f))$ satisfies $x \cdot (f^n|_{D(f)}) = y|_{D(f)}$ for some $n \in \mathbb{N}$ and some $y \in \Gamma(Z, \iota^{-1}U)$, and every $y \in \Gamma(Z,\iota^{-1}U)$ with $y|_{D(f)} = 0$ is annihilated by $f^n$ for some $n$. Third, support: for every affine open $U$ of $V$ with $U \cap \iota(Z) = \emptyset$, the module $\Gamma(Z, \iota^{-1}U)$ is a subsingleton; here $\iota(Z)$ is the range of the underlying map of $\iota$, closed because a closed immersion is a closed embedding.
--
--   This is the standard fact that the direct image of the structure sheaf along a closed immersion is a coherent, quasi-coherent $\mathcal{O}_V$-module supported on the image, recorded for the project's open-by-open presheaf data. It feeds the dévissage computations of Euler characteristics of twists, being used in the results on $\chi$ of twisted tensor powers and on twists of `pushforwardUnit`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.OModulePresheaf.isCoherent_isQuasicoherent_supportedIn_pushforwardUnit
    {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V) [IsClosedImmersion ι] :
    (OModulePresheaf.pushforwardUnit π ι).IsCoherent ∧ (OModulePresheaf.pushforwardUnit π ι).IsQuasicoherent ∧
      (OModulePresheaf.pushforwardUnit π ι).SupportedIn ⟨Set.range ι.base, ι.isClosedEmbedding.isClosed_range⟩ := by sorry
