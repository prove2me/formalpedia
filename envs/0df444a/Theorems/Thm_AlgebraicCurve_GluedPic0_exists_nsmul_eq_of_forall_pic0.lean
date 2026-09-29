-- Prove2me | Theorems.Thm_AlgebraicCurve_GluedPic0_exists_nsmul_eq_of_forall_pic0
-- name    : AlgebraicCurve.GluedPic0.exists_nsmul_eq_of_forall_pic0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/2b7936f6-b818-5286-88a0-eb9b244fdb33
-- title:
--   n-divisibility passes to the glued degree-zero class group
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure satisfying `HasPrincipalDivisors K F`, i.e. every nonzero $f \in F$ has an associated divisor, namely a finitely supported function on the places of $F/K$ whose value at each place $v$ is $v.\mathrm{ord}\,f$ and whose degree is $0$ (a place being a proper valuation subring of $F$ containing the image of $K$ and which is a principal ideal ring). Let $S$ be a finite set of ordered pairs of places of $F/K$, and assume for each $s \in S$ that both structure maps $K \to$ `(s.1).ResidueField` and $K \to$ `(s.2).ResidueField` are surjective, so that both members of each pair are $K$-rational. Let $n$ be a nonzero natural number and suppose $\mathrm{Pic}^0(F/K)$ — the group of degree-zero divisors modulo principal divisors — is $n$-divisible: every class $c$ is of the form $n \cdot c'$. Then for every element $g$ of `GluedPic0 K F S`, the quotient of the group of admissible gluing data (pairs of degree-zero divisors together with a function $S \to \mathrm{Additive}\,K^{\times}$, the first divisor vanishing at each $s.1$ and the second at each $s.2$) by the subgroup of glued principal data, there exists $h$ with $n \cdot h = g$.
--
--   The group `GluedPic0 K F S` models the degree-zero Picard group of a curve obtained by gluing two copies of the curve with function field $F$ along the finite set $S$ of pairs of $K$-rational points, in the spirit of the generalised Jacobians of singular curves; the statement transfers $n$-divisibility from the class group of one component to the glued group. It is used in the construction of torsion preimages under the component map for place specialisations on modular curves, and in the corresponding divisibility statement for $X_1$ models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_GluedPic0_exists_nsmul_eq_of_forall_pic0.lean

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.GluedPic0.exists_nsmul_eq_of_forall_pic0
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (S : Finset (Place K F × Place K F))
    (hrat : ∀ s : ↥S,
      Function.Surjective (algebraMap K ((s : Place K F × Place K F).1.ResidueField)) ∧
        Function.Surjective (algebraMap K ((s : Place K F × Place K F).2.ResidueField)))
    (n : ℕ) (hn : n ≠ 0) (hdiv : ∀ c : Pic0 K F, ∃ c' : Pic0 K F, n • c' = c)
    (g : GluedPic0 K F S) :
    ∃ h : GluedPic0 K F S, n • h = g := by sorry
