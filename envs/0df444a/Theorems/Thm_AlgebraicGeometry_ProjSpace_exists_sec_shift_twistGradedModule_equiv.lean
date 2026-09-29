-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv
-- name    : AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/d8c4596b-60c1-5e10-893d-ed1458741e20
-- title:
--   Twist-datum sections over U_I as graded localisations
-- statement:
--   Fix a commutative ring $A$, a natural number $N$, a scheme $X$, a morphism $\varphi \colon X \to \operatorname{Proj}$ of the graded algebra of homogeneous submodules of $A[x_0,\dots,x_N]$ which is assumed to be an affine morphism, a morphism $\pi \colon X \to \operatorname{Spec} A$ (through which $A$ acts on sections), and $m \in \mathbb{N}$. Write $U_i = \varphi^{-1}(D_+(x_i))$ for `ProjSpace.pullbackChart φ i`. The assertion is that there exists a family $e$ of $A$-linear isomorphisms, one for each nonempty $I \subseteq \{0,\dots,N\}$, from the degree-zero part of the localisation at the variables indexed by $I$ of the $m$-shifted graded module `ProjSpace.twistGradedModule φ π` — concretely, the quotient of fractions with denominator exponents supported on $I$ and numerator in the grade equal to the exponent sum, where grading is shifted by $m$ — onto `ProjSpace.twistObj π φ m (⨅ i ∈ I, pullbackChart φ i)`, the module of families $(g_{i})_{i}$ with $g_i \in \Gamma(X, U_I \cap U_i)$ satisfying the cocycle relation $g_i = u_{ij}^{m} g_j$ on triple overlaps; and that this family is compatible with inclusions: for nonempty $I \subseteq J$, $e_J$ composed with the inclusion map [`ProjSpaceCech.GradedModule.secIncl`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L345) on fractions agrees with restriction `ProjSpace.twistRes` along $U_J \le U_I$ composed with $e_I$.
--
--   This is the commutative-algebra half of the identification of the Čech complex of $\varphi^{*}\mathcal{O}(m)$ on the pulled-back standard cover of $\mathbb{P}^N_A$ with the Čech complex of the associated graded module, in the style of Hartshorne II.5.14. It is used in the vanishing/degeneration step [`AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist`](thm.html#AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ]
    (π : X ⟶ Spec (.of A)) (m : ℕ) :
    ∃ e : ∀ (I : Finset (Fin (N + 1))), I.Nonempty →
        (ProjSpaceCech.GradedModule.sec ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) I
          ≃ₗ[A] ProjSpace.twistObj π φ m (⨅ i ∈ I, ProjSpace.pullbackChart φ i)),
      ∀ (I J : Finset (Fin (N + 1))) (hI : I.Nonempty) (hIJ : I ⊆ J)
        (x : ProjSpaceCech.GradedModule.sec ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) I),
        e J (hI.mono hIJ) (ProjSpaceCech.GradedModule.secIncl _ hIJ x)
          = ProjSpace.twistRes π φ m
              (le_iInf fun i => le_iInf fun hi => (iInf_le _ i).trans (iInf_le _ (hIJ hi)) :
                (⨅ i ∈ J, ProjSpace.pullbackChart φ i) ≤ ⨅ i ∈ I, ProjSpace.pullbackChart φ i)
              (e I hI x) := by sorry
