-- Prove2me | Theorems.Thm_CurveSymmetry_family_isIntegral_iff
-- name    : CurveSymmetry.family_isIntegral_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:13.625189+00:00
-- url     : https://prove2.me/theorems/f3a1801c-3b39-4465-b62f-f53397a9cf38
-- title:
--   Integral closure of $\mathbb C[t]$ in $\mathbb C(t)[W]/(W^2-h_\alpha)$: exactly the elements $a(t)+b(t)\,w$
-- statement:
--   Let $m\ge 1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$ (that is, $\alpha$ is not real), and let $h_\alpha(t)=-t\,(t^m+1)\,(\alpha t^m+\bar\alpha)\in\mathbb C[t]$. Let $L_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$, with $w$ the class of $W$, regarded as a $\mathbb C[t]$-algebra through $\mathbb C[t]\subset\mathbb C(t)$. Then for every $x\in L_\alpha$,
--
--   $$
--   x\ \text{is integral over}\ \mathbb C[t]\iff x=a(t)+b(t)\,w\ \text{for some}\ a,b\in\mathbb C[t].
--   $$
--
--   In other words, the integral closure of $\mathbb C[t]$ in $L_\alpha$ is $\mathbb C[t]+\mathbb C[t]\,w$.
--
--   $L_\alpha$ is the function field of $V_\alpha$ in the form of the double cover (7) from the proof of Lemma 4. The statement identifies the coordinate ring of the normalization of $V_\alpha$ over the affine $t$-line, as part of the description of that normalization as a double cover of the $t$-line.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, equation (7), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuadraticIntegralClosure.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
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

theorem CurveSymmetry.family_isIntegral_iff {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α)
    (x : QuadField (familyH m α)) :
    IsIntegral ℂ[X] x ↔ ∃ a b : ℂ[X], x = algebraMap ℂ[X] (QuadField (familyH m α)) a +
      algebraMap ℂ[X] (QuadField (familyH m α)) b *
        AdjoinRoot.root (quadRat (familyH m α)) := by sorry
