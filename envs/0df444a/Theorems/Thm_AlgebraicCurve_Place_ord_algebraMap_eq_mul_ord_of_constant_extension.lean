-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap_eq_mul_ord_of_constant_extension
-- name    : AlgebraicCurve.Place.ord_algebraMap_eq_mul_ord_of_constant_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/908919e7-5380-5d44-9c71-fbb48ad06ba7
-- title:
--   Ramification index preserved under separable constant extension
-- statement:
--   Let $k \subseteq K$ be fields with $K$ algebraic and separable over $k$, let $E \subseteq F$ be field extensions of $k$ and $E' \subseteq F'$ field extensions of $K$, all linked by $k$-algebra structures arranged into compatible scalar towers, together with maps $E \to E'$ and $F \to F'$. Assume the square commutes, in the sense that for every $e \in E$ the images of $e$ in $F'$ via $F$ and via $E'$ agree; assume $E'$ is generated over $E$ by the image of $K$, i.e. $\mathrm{adjoin}_E(\mathrm{range}(K \to E')) = \top$, and likewise $F'$ is generated over $F$ by the image of $K$. Let $x$, $y$, $x'$, $y'$ be places of $F/k$, $E/k$, $F'/K$, $E'/K$ respectively, a place here being a valuation subring containing the image of the base field, distinct from the whole field, and a principal ideal ring, with $\mathrm{ord}$ the associated normalised integer valuation. Assume the valuation subring of $x'$ pulls back along $F \to F'$ to that of $x$, that of $y'$ pulls back along $E \to E'$ to that of $y$, and that of $x'$ pulls back along $E' \to F'$ to that of $y'$. Let $n \in \mathbb{N}$ and $u \in E$ satisfy $\mathrm{ord}_y(u) = 1$ and $\mathrm{ord}_x(u) = n$ in $F$. Then for every $f \in E'$, $\mathrm{ord}_{x'}$ of the image of $f$ in $F'$ equals $n \cdot \mathrm{ord}_{y'}(f)$.
--
--   This is the statement that a separable algebraic constant-field extension leaves ramification indices unchanged: the ramification index $e(x' \mid y')$ computed upstairs equals the index $n = e(x \mid y)$ read off downstairs from a uniformiser $u$ at $y$. It feeds the construction of places with prescribed ramification behaviour in [`AlgebraicCurve.Place.exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow`](thm.html#AlgebraicCurve.Place.exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_algebraMap_eq_mul_ord_of_constant_extension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_algebraMap_eq_mul_ord_of_constant_extension
    {k K E F E' F' : Type*} [Field k] [Field K] [Field E] [Field F] [Field E'] [Field F']
    [Algebra k K] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K]

    [Algebra k E] [Algebra k F] [Algebra E F] [IsScalarTower k E F]
    [Algebra K E'] [Algebra K F'] [Algebra E' F'] [IsScalarTower K E' F']

    [Algebra E E'] [Algebra F F'] [Algebra k E'] [Algebra k F']
    [IsScalarTower k K E'] [IsScalarTower k E E'] [IsScalarTower k K F'] [IsScalarTower k F F']
    (hsq : ∀ e : E, algebraMap F F' (algebraMap E F e) = algebraMap E' F' (algebraMap E E' e))
    (hgenE : Algebra.adjoin E (Set.range (algebraMap K E')) = ⊤)
    (hgenF : Algebra.adjoin F (Set.range (algebraMap K F')) = ⊤)

    (x : Place k F) (y : Place k E) (x' : Place K F') (y' : Place K E')
    (hx : x'.toValuationSubring.comap (algebraMap F F') = x.toValuationSubring)
    (hy : y'.toValuationSubring.comap (algebraMap E E') = y.toValuationSubring)
    (hx'y' : x'.toValuationSubring.comap (algebraMap E' F') = y'.toValuationSubring)

    (n : ℕ) (u : E) (hu : y.ord u = 1) (hn : x.ord (algebraMap E F u) = n) :
    ∀ f : E', x'.ord (algebraMap E' F' f) = n * y'.ord f := by sorry
