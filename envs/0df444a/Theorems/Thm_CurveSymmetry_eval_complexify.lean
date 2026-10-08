-- Prove2me | Theorems.Thm_CurveSymmetry_eval_complexify
-- name    : CurveSymmetry.eval_complexify
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:31.700717+00:00
-- url     : https://prove2.me/theorems/a2c6f0c5-575d-460b-ba55-4348d12590c6
-- title:
--   The complexification of $P$ evaluated at $(z,\bar z)$ equals $P(\operatorname{Re}z,\operatorname{Im}z)$
-- statement:
--   Let $P\in\mathbb C[X,Y]$ and let $P^{\mathbb C}(X,Y)=P\bigl(\tfrac{X+Y}{2},\tfrac{X-Y}{2i}\bigr)$ be its complexification, which expresses $P$ in the complex coordinates $X=z$, $Y=\bar z$.
--
--   Then for every $z\in\mathbb C$,
--   $$P^{\mathbb C}(z,\bar z)=P(\operatorname{Re}z,\operatorname{Im}z).$$
--
--   Consequently $\{z\in\mathbb C:P^{\mathbb C}(z,\bar z)=0\}$ is the Cartesian zero set $\{x+iy: x,y\in\mathbb R,\ P(x,y)=0\}$. For a real equation $f$ this identifies the curve $C$ with the zero set, in the coordinates $z,\bar z$, of its complexification, which is the description of $C$ used from equation (4) on and in Lemma 3 and Theorems 1 and 2.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 2, equation (4), p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/CartesianCoordinates.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.eval_complexify (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (complexify P) =
      eval (fun i : Fin 2 => if i = 0 then (z.re : ℂ) else (z.im : ℂ)) P := by sorry
