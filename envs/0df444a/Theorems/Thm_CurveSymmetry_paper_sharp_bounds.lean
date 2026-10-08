-- Prove2me | Theorems.Thm_CurveSymmetry_paper_sharp_bounds
-- name    : CurveSymmetry.paper_sharp_bounds
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:55.371545+00:00
-- url     : https://prove2.me/theorems/8a64a90f-baa6-4cd1-b57e-0aa5287ef35c
-- title:
--   Theorem 1 (the bounds): finite groups with $|\mathrm{Sym}^+(C)|\le\max\{d,2d-4\}$ and $|\mathrm{Sym}(C)|\le2d$
-- statement:
--   Let $f\in\mathbb R[x,y]$ be irreducible in $\mathbb C[x,y]$ and of total degree $d\ge2$. Identify $(x,y)$ with $x+iy$ and let $C=\{z\in\mathbb C: f(\operatorname{Re}z,\operatorname{Im}z)=0\}$ be the real zero set of $f$. Assume that $C$ is infinite and is not a circle: there are no $c\in\mathbb C$ and real $R>0$ with $C=\{z\in\mathbb C:|z-c|=R\}$. Let $\mathrm{Sym}(C)$ be the group of Euclidean isometries $T$ of $\mathbb C$ with $T(C)=C$, and $\mathrm{Sym}^+(C)$ its subgroup of maps of the form $z\mapsto az+b$ with $|a|=1$, the orientation-preserving ones.
--
--   Then:
--
--   1. $\mathrm{Sym}(C)$ is finite;
--   2. $\mathrm{Sym}^+(C)$ is finite;
--   3. $\mathrm{Sym}^+(C)$ is cyclic;
--   4. the orders of the two groups satisfy
--
--   $$|\mathrm{Sym}^+(C)|\le\max\{d,\,2d-4\},\qquad|\mathrm{Sym}(C)|\le2d.$$
--
--   These are the finiteness statement and the two bounds of Theorem 1, together with the finiteness and cyclicity assertions of Lemma 3. Sharpness and the equality case are stated separately.
--
--   **Formalization Note**: the curve is a subset of $\mathbb C$; $\mathrm{Sym}(C)$ and $\mathrm{Sym}^+(C)$ are subgroups of the group `ℂ ≃ᵢ ℂ` of isometric bijections of $\mathbb C$, membership meaning $T(z)\in C\iff z\in C$ for all $z$; orders are cardinalities (`Nat.card`).
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Theorem 1, p. 1, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/PaperBounds.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
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

theorem CurveSymmetry.paper_sharp_bounds {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) :
    Finite (isometrySetGroup (cartesianLocus f)) ∧
      Finite (directIsometryGroup (cartesianLocus f)) ∧
      IsCyclic (directIsometryGroup (cartesianLocus f)) ∧
      Nat.card (directIsometryGroup (cartesianLocus f)) ≤ max f.totalDegree (2 * f.totalDegree - 4) ∧
      Nat.card (isometrySetGroup (cartesianLocus f)) ≤ 2 * f.totalDegree := by sorry
