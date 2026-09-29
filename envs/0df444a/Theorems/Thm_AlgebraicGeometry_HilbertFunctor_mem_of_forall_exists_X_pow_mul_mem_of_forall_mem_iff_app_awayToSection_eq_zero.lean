-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero
-- name    : AlgebraicGeometry.HilbertFunctor.mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/a518c391-f02d-5c95-a5d3-5512c16a54da
-- title:
--   Ideals cut out chartwise on Pⁿ_k are variable-saturated
-- statement:
--   Fix $n \in \mathbb{N}$ and a field $k$ (in the zeroth universe), and work on $\operatorname{Proj}$ of the graded ring $k[x_0,\dots,x_n]$ presented by its homogeneous submodules `MvPolynomial.homogeneousSubmodule (Fin (n+1)) k`. Let $\iota_k \colon Z_k \to \operatorname{Proj}$ be a morphism of schemes and let $I$ be an ideal of $k[x_0,\dots,x_n]$ subject to the following hypothesis: for every degree $d$ and every $F$ that is homogeneous of degree $d$, membership $F \in I$ holds if and only if for each index $i \in \{0,\dots,n\}$ the section obtained by applying the structure map of $\iota_k$ on the basic open set $D_+(x_i)$ to the image under `Proj.awayToSection` of the degree-zero homogeneous localisation element $F / x_i^{d}$ is zero. Under this hypothesis, for every $d$ and every $F$ homogeneous of degree $d$ such that for each $i$ there exists $N \in \mathbb{N}$ with $x_i^{N} F \in I$, one concludes $F \in I$. Thus $I$ is saturated with respect to each variable, in the sense stated, on homogeneous elements.
--
--   This is the saturation property of the homogeneous ideal attached to a morphism into projective space by the chartwise vanishing condition: an ideal defined by requiring that $F/x_i^d$ pull back to zero on each standard chart automatically absorbs homogeneous elements all of whose variable multiples already lie in it. It is used in the computation of Hilbert functions of closed subschemes of $\mathbb{P}^n_k$, being cited by [`AlgebraicGeometry.HilbertFunctor.exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq`](thm.html#AlgebraicGeometry.HilbertFunctor.exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero
    (n : ℕ) (k : Type) [Field k]
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hZ : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
          (F ∈ I ↔ ∀ i : Fin (n + 1),
            (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0))
    (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d)
    (hsat : ∀ i : Fin (n + 1), ∃ N : ℕ, MvPolynomial.X i ^ N * F ∈ I) :
    F ∈ I := by sorry
