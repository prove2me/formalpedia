-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq
-- name    : AlgebraicGeometry.HilbertFunctor.exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/61b24a69-972e-5821-b950-24f5c2b6e3c5
-- title:
--   Gotzmann regularity in uniform numerical form
-- statement:
--   Fix $n \in \mathbb{N}$ and a polynomial $P \in \mathbb{Q}[t]$. The assertion is that there is a bound $G \in \mathbb{N}$, depending only on $n$ and $P$ (it is chosen before the field and the subscheme), such that the following holds for every algebraically closed field $k$ (a type in the lowest universe), every scheme $Zk$ and every morphism $\iota_k : Zk \to \operatorname{Proj}$ of the graded ring given by the homogeneous submodules of $k[X_0,\dots,X_n]$ which is a closed immersion, and every ideal $I \subseteq k[X_0,\dots,X_n] =$ `MvPolynomial (Fin (n+1)) k` subject to two hypotheses: first, $I$ is homogeneous in the sense that for every $p \in I$ and every $d$ the degree-$d$ homogeneous component of $p$ again lies in $I$; second, $I$ is exactly the ideal cut out by $\iota_k$ chart by chart, i.e. for every $d$ and every $F$ homogeneous of degree $d$, one has $F \in I$ if and only if for each $i \in \{0,\dots,n\}$ the section of the structure sheaf of $Zk$ obtained by applying $\iota_k$ on the basic open set $D(X_i)$ to the section associated with the homogeneous localisation $F/X_i^{d}$ vanishes. Under these hypotheses, if the function $d \mapsto \dim_k$ of `piece I d`, the quotient of the space of degree-$d$ homogeneous polynomials by its intersection with $I$, agrees with $P(d)$ for all $d$ beyond some threshold $D_0$ (which may depend on $k$, $Zk$ and $I$), then it agrees with $P(d)$ for every $d \ge G$.
--
--   This is the numerical form of Gotzmann's regularity theorem: the Hilbert function of the saturated homogeneous ideal of a closed subscheme of $\mathbb{P}^n_k$ reaches its Hilbert polynomial at a degree bounded in terms of $n$ and the polynomial alone, uniformly in the field and the subscheme. The uniform bound is what allows a single truncation level to be fixed for each Hilbert polynomial, and it is used in the construction of the Hilbert functor's ideal points on geometric fibres and in the uniform covering statement for flat families of finite presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq
    (n : ℕ) (P : Polynomial ℚ) :
    ∃ G : ℕ, ∀ (k : Type) [Field k] [IsAlgClosed k]
      (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)), IsClosedImmersion ιk →
      ∀ (I : Ideal (MvPolynomial (Fin (n + 1)) k)),
        (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) →
        (∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
          (F ∈ I ↔ ∀ i : Fin (n + 1),
            (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0)) →
        (∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ)) →
        ∀ d : ℕ, G ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ) := by sorry
