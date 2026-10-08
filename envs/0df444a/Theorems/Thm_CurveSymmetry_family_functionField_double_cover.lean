-- Prove2me | Theorems.Thm_CurveSymmetry_family_functionField_double_cover
-- name    : CurveSymmetry.family_functionField_double_cover
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:22.660795+00:00
-- url     : https://prove2.me/theorems/b79ec60d-db0f-4ea1-a25c-4a7a36f184ab
-- title:
--   The function field of $V_\alpha$ is $\mathbb C(t)[W]/(W^2-h_\alpha)$, with $t=X/Y$ and $W\mapsto t(t^m+1)Y$
-- statement:
--   Let $m\ge 1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$. Let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)\in\mathbb C[X,Y]$, and let $K$ be the field of fractions of $\mathbb C[X,Y]/(P_\alpha)$, the function field of the curve $P_\alpha=0$ (whose closure in $\mathbb P^1\times\mathbb P^1$ is $V_\alpha$). Write $x,y\in K$ for the classes of $X,Y$, and put $t=x/y$ and $w=t\,(t^m+1)\,y$ in $K$. Let $h_\alpha(t)=-t\,(t^m+1)\,(\alpha t^m+\bar\alpha)\in\mathbb C[t]$, let $L_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$, and let $\iota\colon\mathbb C(t)\to K$ be the $\mathbb C$-algebra homomorphism $p(t)/q(t)\mapsto p(x/y)/q(x/y)$.
--
--   Then there is a ring isomorphism
--
--   $$
--   e\colon\ L_\alpha=\mathbb C(t)[W]/\big(W^2-h_\alpha(t)\big)\ \xrightarrow{\ \sim\ }\ K,\qquad e(r)=\iota(r)\ \ (r\in\mathbb C(t)),\qquad e(W)=w,
--   $$
--
--   and moreover:
--
--   1. $h_\alpha$ has degree $2m+1$ and is squarefree;
--   2. $W^2-h_\alpha(t)$ is irreducible in $\mathbb C(t)[W]$, and $L_\alpha$ has dimension $2$ over $\mathbb C(t)$;
--   3. $\iota(t)=x/y$;
--   4. $w^2=h_\alpha(x/y)$ in $K$.
--
--   This is the double cover (7) from the proof of Lemma 4, read on function fields: multiplying (7) by $t(t^m+1)$ turns it into $w^2=h_\alpha(t)$ with $w=t(t^m+1)Y$. The normalization of $V_\alpha$ is represented by this function field when the genus in Lemma 4 is computed.
--
--   **Formalization Note**: $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instances, and $K$ is Mathlib's `FractionRing` of the quotient ring, that is, its localization at the non-zero-divisors.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), proof of Lemma 4, equation (7), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyFunctionField.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ}
variable [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

theorem CurveSymmetry.family_functionField_double_cover :
    (familyH m α).natDegree = 2 * m + 1 ∧ Squarefree (familyH m α) ∧
      Irreducible (familyQuadraticRat m α) ∧
      Module.finrank (RatFunc ℂ) (AdjoinRoot (familyQuadraticRat m α)) = 2 ∧
      familyRatFuncHom m α RatFunc.X = familyT m α ∧
      familyW m α ^ 2 = aeval (familyT m α) (familyH m α) ∧
      ∃ e : AdjoinRoot (familyQuadraticRat m α) ≃+* FamilyFunctionField m α,
        (∀ r, e (AdjoinRoot.of _ r) = familyRatFuncHom m α r) ∧
        e (AdjoinRoot.root _) = familyW m α := by sorry
