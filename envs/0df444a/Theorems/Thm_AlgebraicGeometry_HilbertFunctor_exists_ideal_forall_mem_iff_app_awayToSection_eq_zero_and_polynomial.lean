-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial
-- name    : AlgebraicGeometry.HilbertFunctor.exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/10078fa9-1184-5b54-b221-3d266b5e5701
-- title:
--   Hilbert–Serre for a closed subscheme of Pⁿ_k
-- statement:
--   Fix a natural number $n$ and a field $k$, and let $\iota_k : Z_k \to \operatorname{Proj}$ of the graded ring $k[x_0,\dots,x_n] = \mathrm{MvPolynomial}\,(\mathrm{Fin}\,(n+1))\,k$, graded by the submodules `MvPolynomial.homogeneousSubmodule`, be a morphism of schemes that is a closed immersion. The assertion is that there exists an ideal $I \subseteq k[x_0,\dots,x_n]$ with three properties. First, $I$ is homogeneous in the sense that for every $p \in I$ and every $d$ the degree-$d$ homogeneous component of $p$ again lies in $I$. Second, $I$ is cut out by vanishing on $Z_k$ chart by chart: for every $d$ and every $F$ homogeneous of degree $d$, one has $F \in I$ if and only if for each $i \in \mathrm{Fin}\,(n+1)$ the image of the section $F/x_i^{d}$ — the homogeneous localisation of degree-$d$ numerator $F$ and denominator $x_i^{d}$, viewed via `Proj.awayToSection` as a section of the structure sheaf over the basic open set $D_+(x_i)$ — under the map $\iota_k$ induces on sections over $D_+(x_i)$ is zero. Third, the Hilbert function of the quotient is eventually polynomial: there are $P \in \mathbb{Q}[t]$ and $D_0 \in \mathbb{N}$ such that for all $d \ge D_0$ the $k$-dimension of `piece I d`, namely the space of degree-$d$ forms modulo those lying in $I$, equals $P(d)$.
--
--   This is the Hilbert–Serre theorem in the form needed for the Hilbert functor: a closed subscheme of $\mathbb{P}^n$ over a field has a saturated homogeneous ideal, described by vanishing of $F/x_i^d$ on each standard chart, and the Hilbert function of the quotient agrees with a rational polynomial in large degrees. It is used in the construction of the stratification of the Hilbert functor by Hilbert polynomial, in particular by [`AlgebraicGeometry.HilbertFunctor.exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing`](thm.html#AlgebraicGeometry.HilbertFunctor.exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing) and in showing that the framed polarised abelian scheme functor is empty when no Hilbert polynomial exists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial
    (n : ℕ) (k : Type) [Field k]
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (hιk : IsClosedImmersion ιk) :
    ∃ (I : Ideal (MvPolynomial (Fin (n + 1)) k)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      (∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ I ↔ ∀ i : Fin (n + 1),
                  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
                    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                      (HomogeneousLocalization.mk
                        { deg := d
                          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                            (MvPolynomial.isHomogeneous_X_pow i d)⟩
                          den_mem := ⟨d, rfl⟩ })) = 0)) ∧
      ∃ (P : Polynomial ℚ) (D₀ : ℕ), ∀ d : ℕ, D₀ ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ) := by sorry
