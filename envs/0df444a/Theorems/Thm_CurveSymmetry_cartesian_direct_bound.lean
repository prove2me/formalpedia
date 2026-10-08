-- Prove2me | Theorems.Thm_CurveSymmetry_cartesian_direct_bound
-- name    : CurveSymmetry.cartesian_direct_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:37.12945+00:00
-- url     : https://prove2.me/theorems/03701f3f-126b-4270-b12c-385af62623f4
-- title:
--   At most $\max\{d,2d-4\}$ direct symmetries $z\mapsto az+b$ for a real algebraic curve of degree $d$, not a circle
-- statement:
--   Let $f\in\mathbb R[x,y]$ be irreducible in $\mathbb C[x,y]$ and of total degree $d\ge2$. Identify $(x,y)$ with $x+iy$ and let $C=\{z\in\mathbb C: f(\operatorname{Re}z,\operatorname{Im}z)=0\}$ be the real zero set of $f$. Assume that $C$ is infinite and that $C$ is not a circle: there are no $c\in\mathbb C$ and real $R>0$ with $C=\{z\in\mathbb C:|z-c|=R\}$. Let $D$ be the set of pairs $(a,b)\in\mathbb C^2$ with $|a|=1$ such that $az+b\in C\iff z\in C$ for every $z\in\mathbb C$, i.e. such that the orientation-preserving isometry $z\mapsto az+b$ maps $C$ onto itself.
--
--   Then $D$ is finite and
--   $$|D|\le\max\{d,\,2d-4\}.$$
--
--   Distinct pairs give distinct maps, so $D$ is in bijection with $\mathrm{Sym}^+(C)$, and this is the rotation bound $N\le\max\{d,2d-4\}$ of Theorem 1, stated, as in the note, for a real Cartesian polynomial.
--
--   **Formalization Note**: the curve is a subset of $\mathbb C$, and $D$ is a set of parameter pairs rather than a group of maps; irreducibility of $f$ in $\mathbb C[x,y]$ is irreducibility of its image under the inclusion $\mathbb R[x,y]\subset\mathbb C[x,y]$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 2, equation (4), p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/CartesianReal.lean (C. Perassi)

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

theorem CurveSymmetry.cartesian_direct_bound {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) :
    Finite (CartesianDirectSymmetries f) ∧
      Nat.card (CartesianDirectSymmetries f) ≤ max f.totalDegree (2 * f.totalDegree - 4) := by sorry
