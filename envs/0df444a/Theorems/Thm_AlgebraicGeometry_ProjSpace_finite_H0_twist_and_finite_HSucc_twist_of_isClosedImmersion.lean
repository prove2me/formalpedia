-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion
-- name    : AlgebraicGeometry.ProjSpace.finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/b09d8525-5614-5cc9-bf76-89f1beba4eac
-- title:
--   Finiteness of Čech cohomology of twists on closed subschemes of Pⁿ_A
-- statement:
--   Let $A$ be a commutative Noetherian ring, $n$ a natural number, $Z$ a scheme, and let $\iota : Z \to \operatorname{Proj}$ of the graded ring $A[x_0,\dots,x_n]$ (given as the homogeneous submodules of `MvPolynomial (Fin (n+1)) A`) be a closed immersion; let $d$ be a natural number. Consider the $A$-module presheaf `ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d` on $Z$ over the composite structure morphism $Z \to \operatorname{Proj} \to \operatorname{Spec} A$: its sections over an open $U \subseteq Z$ are the families $(g_i)_{i \in \mathrm{Fin}(n+1)}$ with $g_i \in \Gamma(Z, U \cap \iota^{-1}D(x_i))$ satisfying the compatibility condition `TwistCompat` of weight $d$, with restriction given by restriction of sections. Take the ordered affine cover `ProjSpace.stdCoverPullback ι` of $Z$, indexed by $\mathrm{Fin}(n+1)$ (lifted to universe $u$), whose members are the preimages $\iota^{-1}D(x_j)$ of the standard basic opens, each affine and together covering $Z$. The conclusion is twofold: the degree-zero Čech group, namely the kernel of the first differential on $0$-cochains of this presheaf for this cover, is a finite $A$-module, and for every $i$ the subquotient $\ker d_{i+1} / \operatorname{im} d_i$, i.e. the Čech cohomology in degree $i+1$, is a finite $A$-module.
--
--   This is the finiteness theorem for the cohomology of $\mathcal{O}_Z(d)$ on a closed subscheme $Z \subseteq \mathbb{P}^n_A$ over a Noetherian base, in the Čech form attached to the pulled-back standard cover (EGA III 2.2.2, Hartshorne III.5.2). It feeds the construction of points of the Hilbert functor, being cited in the identification of a point with a saturated homogeneous ideal for closed immersions that are flat and locally of finite presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion
    {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι] (d : ℕ) :
    Module.Finite A ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι)) ∧
    (∀ i : ℕ, Module.Finite A ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).HSucc (ProjSpace.stdCoverPullback ι) i)) := by sorry
