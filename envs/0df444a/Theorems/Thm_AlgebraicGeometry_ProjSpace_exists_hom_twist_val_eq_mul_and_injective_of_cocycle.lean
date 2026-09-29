-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_hom_twist_val_eq_mul_and_injective_of_cocycle
-- name    : AlgebraicGeometry.ProjSpace.exists_hom_twist_val_eq_mul_and_injective_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/7183407b-1d62-5f58-a708-a198a2b89bb2
-- title:
--   Multiplication by a weight-e cocycle twists O(d) into O(d+e)
-- statement:
--   Let $A$ be a commutative ring, $N$ a natural number, $Z$ a scheme, $\pi : Z \to \operatorname{Spec} A$ a morphism, and $\iota : Z \to \operatorname{Proj}$ of the graded ring of polynomials in $N+1$ variables over $A$ (that is, $\mathbb P^N_A$) an affine morphism. Write $U_i = \iota^{-1}D_+(x_i)$ for `ProjSpace.pullbackChart ι i` and $u_{ij} \in \Gamma(Z, U_i)$ for `ProjSpace.frameUnit ι i j`, the image under $\iota^\sharp$ of the degree-zero element $x_j/x_i$ of the localisation away from $x_i$. Fix $e \in \mathbb N$ and sections $t_i \in \Gamma(Z, U_i)$, for $i \in \{0,\dots,N\}$, subject to the weight-$e$ cocycle condition: for all $i, j$ the restrictions to $U_i \cap U_j$ satisfy $t_i| = (u_{ij}|)^e \cdot t_j|$, the restriction maps being the ring homomorphisms `ProjSpace.restrictFun`. Assume further that each $t_i$ is a non-zero-divisor in $\Gamma(Z, U_i)$, stated as: $t_i y = 0$ implies $y = 0$. Then for every $d \in \mathbb N$ there exists a morphism $\mu$ of the presheaves of modules `ProjSpace.twist π ι d` and `ProjSpace.twist π ι (d+e)` — i.e. a family of $A$-linear maps $\mu_U$, one for each open $U \subseteq Z$, each $\Gamma(Z,U)$-semilinear in the sense $\mu_U(a \cdot x) = a \cdot \mu_U(x)$ and commuting with all restriction maps — such that for every open $U$, every element $g$ of the $d$-th twist over $U$, given by components $g_i \in \Gamma(Z, U \cap U_i)$ satisfying the compatibility predicate `TwistCompat ι d U`, and every index $i$, the $i$-th component of $\mu_U(g)$ is the restriction of $t_i$ to $U \cap U_i$ times $g_i$; and such that $\mu_U$ is injective for every open $U \subseteq Z$.
--
--   This realises multiplication by a global section of $\mathcal O_Z(e)$, written in the standard frames of the charts $U_i$, as an injection $\mathcal O_Z(d) \to \mathcal O_Z(d+e)$ of the frame model of the twisting presheaves. It is used by [`AlgebraicGeometry.ProjSpace.exists_affSES_twist_succ_of_forall_mul_eq_zero_imp`](thm.html#AlgebraicGeometry.ProjSpace.exists_affSES_twist_succ_of_forall_mul_eq_zero_imp) to produce the short exact sequences of twists on which the cohomological arguments over projective space rest.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_hom_twist_val_eq_mul_and_injective_of_cocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.ProjSpace.exists_hom_twist_val_eq_mul_and_injective_of_cocycle
    {A : Type u} [CommRing A] {N : ℕ} {Z : Scheme.{u}}
    (π : Z ⟶ Spec (.of A)) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom ι]
    (e : ℕ) (t : ∀ i : Fin (N + 1), Γ(Z, ProjSpace.pullbackChart ι i))
    (htc : ∀ i j : Fin (N + 1),
      ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ι i ⊓ ProjSpace.pullbackChart ι j ≤ _) (t i)
        = ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ι i ⊓ ProjSpace.pullbackChart ι j ≤ _)
            (ProjSpace.frameUnit ι i j) ^ e
          * ProjSpace.restrictFun (inf_le_right : ProjSpace.pullbackChart ι i ⊓ ProjSpace.pullbackChart ι j ≤ _) (t j))
    (hnz : ∀ (i : Fin (N + 1)) (y : Γ(Z, ProjSpace.pullbackChart ι i)), t i * y = 0 → y = 0) (d : ℕ) :
    ∃ μ : OModulePresheaf.Hom (ProjSpace.twist π ι d) (ProjSpace.twist π ι (d + e)),
      (∀ (U : Z.Opens) (g : (ProjSpace.twist π ι d).obj U) (i : Fin (N + 1)),
        (μ.app U g).val i
          = ProjSpace.restrictFun (inf_le_right : U ⊓ ProjSpace.pullbackChart ι i ≤ _) (t i) * g.val i) ∧
      (∀ U : Z.Opens, Function.Injective (μ.app U)) := by sorry
