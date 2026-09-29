-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_tensor_eq_of_inPicZero_of_kernelPts_finite
-- name    : AlgebraicGeometry.Polarisation.geomFibreH0Finrank_tensor_eq_of_inPicZero_of_kernelPts_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c2d9abf0-257e-562e-b5b0-9725f5f2f7ec
-- title:
--   Twisting by Pic⁰ preserves h⁰ of a nondegenerate line bundle
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, compatible with base change in $T$; assume $L$ is commutative and that $f$ satisfies `AbelianSchemePropertyBundle`, that is, $f$ is smooth and proper with connected fibres and admits some relative group law. Let $g$ be a natural number such that every fibre $f^{-1}(s)$, for $s$ a point of $\operatorname{Spec} k$, has topological Krull dimension $g$. Let $\mathcal M$ be a module on $A$ which is invertible (locally isomorphic to the unit module), and assume the set `kernelPts` of those $k$-points $x$ of $A$ for which $\mathcal M$ lies in the stabiliser of $x$ (the pullbacks of $\mathcal M$ along right multiplication by $x$ and along the first projection being locally isomorphic over the base) is finite. Let $P$ be a module on $A$ with `InPicZero`: $P$ is invertible and for every $k$-point $x$ the pullback of $P$ along the translation $L.\mathrm{translate}\,x$ is isomorphic to $P$. Finally let $k'$ be an algebraically closed field and $sk : k \to k'$ a ring homomorphism. Then the $k'$-dimension of the global sections of the pullback of $\mathcal M \otimes P$ to the base change $A \times_{\operatorname{Spec} k} \operatorname{Spec} k'$ equals that for $\mathcal M$: $\mathrm{geomFibreH0Finrank}\,f\,(\mathcal M \otimes P)\,k'\,sk = \mathrm{geomFibreH0Finrank}\,f\,\mathcal M\,k'\,sk$.
--
--   This is the degree-zero, cohomology-free part of the invariance of $h^0$ under twisting by an element of $\mathrm{Pic}^0$ of an abelian variety, for a line bundle with finite kernel; classically it accompanies Mumford's theorem that such a bundle's translates exhaust its $\mathrm{Pic}^0$-twists. It is used in the positivity statement for geometric $h^0$ of tensor powers twisted by $\mathrm{Pic}^0$ in the polarisation development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_tensor_eq_of_inPicZero_of_kernelPts_finite.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.geomFibreH0Finrank_tensor_eq_of_inPicZero_of_kernelPts_finite
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (hK : (kernelPts f L 𝓜).Finite)
    (P : A.Modules) (hP : InPicZero f L P)
    (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') :
    Scheme.Modules.geomFibreH0Finrank f (𝓜 ⊗ P) k' sk = Scheme.Modules.geomFibreH0Finrank f 𝓜 k' sk := by sorry
