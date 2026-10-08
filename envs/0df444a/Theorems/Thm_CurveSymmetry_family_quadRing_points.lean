-- Prove2me | Theorems.Thm_CurveSymmetry_family_quadRing_points
-- name    : CurveSymmetry.family_quadRing_points
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:31.741871+00:00
-- url     : https://prove2.me/theorems/17a7c46e-72be-40ec-9ced-07df413edf9a
-- title:
--   $\mathbb C[t][W]/(W^2-h_\alpha)$ embeds onto the integral closure of $\mathbb C[t]$; its maximal ideals are the points
-- statement:
--   Let $m\ge 1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$ (that is, $\alpha$ is not real), and let $h_\alpha(t)=-t\,(t^m+1)\,(\alpha t^m+\bar\alpha)\in\mathbb C[t]$. Let $R=\mathbb C[t][W]/(W^2-h_\alpha(t))$ and $L_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$, with $w$ the class of $W$ in $L_\alpha$, and let $\varphi\colon R\to L_\alpha$ be the $\mathbb C[t]$-algebra homomorphism with $\varphi(W)=w$. For $c,d\in\mathbb C$ with $d^2=h_\alpha(c)$, let $\operatorname{ev}_{c,d}\colon R\to\mathbb C$ be the evaluation $t\mapsto c$, $W\mapsto d$. Then:
--
--   1. $\varphi$ is injective;
--   2. an element $x\in L_\alpha$ is integral over $\mathbb C[t]$ if and only if $x=\varphi(y)$ for some $y\in R$;
--   3. an ideal $\mathfrak m$ of $R$ is maximal if and only if $\mathfrak m=\ker\operatorname{ev}_{c,d}$ for some $c,d\in\mathbb C$ with $d^2=h_\alpha(c)$.
--
--   Parts 1 and 2 say that $\varphi$ identifies $R$ with the integral closure of $\mathbb C[t]$ in $L_\alpha$:
--
--   $$
--   \varphi\colon\ \mathbb C[t][W]/\big(W^2-h_\alpha(t)\big)\ \xrightarrow{\ \sim\ }\ \{x\in L_\alpha:\ x\ \text{integral over}\ \mathbb C[t]\}.
--   $$
--
--   In terms of the double cover (7) from the proof of Lemma 4, whose function field is $L_\alpha$, this describes the normalization of $V_\alpha$ over the affine $t$-line: its coordinate ring is $R$, and its points are the pairs $(c,d)$ with $d^2=h_\alpha(c)$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, equation (7), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuadraticRing.lean (C. Perassi)

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

theorem CurveSymmetry.family_quadRing_points {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    Function.Injective (quadRingMap (familyH m α)) ∧
      (∀ x : QuadField (familyH m α),
        IsIntegral ℂ[X] x ↔ ∃ y, quadRingMap (familyH m α) y = x) ∧
      ∀ 𝔪 : Ideal (QuadRing (familyH m α)), 𝔪.IsMaximal ↔
        ∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c),
          𝔪 = RingHom.ker (quadEval (familyH m α) c d hd) := by sorry
