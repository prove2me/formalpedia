-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal
-- name    : AlgebraicGeometry.ProjSpace.exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/dbc2f379-542a-54e7-8538-2259eafd57c8
-- title:
--   Chartwise spreading of ideal-sheaf membership on Pⁿ_A
-- statement:
--   Fix $n \in \mathbb{N}$ and a commutative ring $A$, and let $\mathbb{P}^n_A$ be realised as $\operatorname{Proj}$ of the graded ring $A[x_0,\dots,x_n]$ with its submodules of homogeneous polynomials as grading. Let $\mathcal{I}$ be an `IdealSheafData` on this scheme, i.e. a quasi-coherent ideal sheaf presented by assigning to each affine open $U$ an ideal $\mathcal{I}.\mathrm{ideal}(U)$ of $\Gamma(U,\mathcal{O})$, compatibly. Let $i$ be an index in $\mathrm{Fin}(n+1)$, let $a \in \mathbb{N}$ and let $H \in A[x_0,\dots,x_n]$ be homogeneous of degree $a$. Assume that the section of $\mathcal{O}$ over the basic open $D_+(x_i)$ obtained, via `Proj.awayToSection`, from the degree-zero homogeneous localisation element with numerator $H$ and denominator $x_i^a$ (both of degree $a$) lies in $\mathcal{I}.\mathrm{ideal}$ of the affine open $D_+(x_i)$, this open being affine because $x_i$ is homogeneous of degree $1 > 0$. Then for every $N_0 \in \mathbb{N}$ there is an $N \geq N_0$ such that for every index $j$ the section over $D_+(x_j)$ determined by the fraction $x_i^N H / x_j^{N+a}$, of numerator and denominator degree $N + a$, lies in $\mathcal{I}.\mathrm{ideal}$ of the affine open $D_+(x_j)$.
--
--   This is the saturation step in the comparison of a quasi-coherent ideal sheaf on projective space with a homogeneous ideal: membership of a fraction in the ideal on one standard chart propagates, after multiplication by a sufficiently high power of the corresponding coordinate, to every standard chart. It is used in the identification of the ideal sheaf of a closed immersion into $\mathbb{P}^n_A$ with the kernel of the associated map of graded rings, and in the vanishing statement for sections multiplied by a linear form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal
    (n : ℕ) (A : Type) [CommRing A] (𝓘 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).IdealSheafData)
    (i : Fin (n + 1)) (a : ℕ) (H : MvPolynomial (Fin (n + 1)) A) (hH : H.IsHomogeneous a)
    (hmem : (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
      (HomogeneousLocalization.mk
        { deg := a
          num := ⟨H, (MvPolynomial.mem_homogeneousSubmodule a H).mpr hH⟩
          den := ⟨X i ^ a, (MvPolynomial.mem_homogeneousSubmodule a _).mpr (MvPolynomial.isHomogeneous_X_pow i a)⟩
          den_mem := ⟨a, rfl⟩ }) ∈
      𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩)
    (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∀ j : Fin (n + 1),
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j))
        (HomogeneousLocalization.mk
          { deg := N + a
            num := ⟨X i ^ N * H, (MvPolynomial.mem_homogeneousSubmodule (N + a) _).mpr ((MvPolynomial.isHomogeneous_X_pow i N).mul hH)⟩
            den := ⟨X j ^ (N + a), (MvPolynomial.mem_homogeneousSubmodule (N + a) _).mpr (MvPolynomial.isHomogeneous_X_pow j (N + a))⟩
            den_mem := ⟨N + a, rfl⟩ }) ∈
        𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j) (ProjSpace.X_mem_one A n j) one_pos⟩ := by sorry
