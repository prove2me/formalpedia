-- Prove2me | Theorems.Thm_CurveSymmetry_paper_full_sharp
-- name    : CurveSymmetry.paper_full_sharp
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:06.191439+00:00
-- url     : https://prove2.me/theorems/6e3b2708-0d28-428b-a7b3-4edd983194e4
-- title:
--   Theorem 1 (sharpness of the full bound): $|\mathrm{Sym}(C)|=2d$ occurs in every degree $d\ge2$
-- statement:
--   Let $d\ge2$ be an integer. For $f\in\mathbb R[x,y]$ let $C=\{z\in\mathbb C: f(\operatorname{Re}z,\operatorname{Im}z)=0\}$ be its real zero set, identifying $(x,y)$ with $x+iy$, and let $\mathrm{Sym}(C)$ be the group of all Euclidean isometries $T$ of $\mathbb C$ with $T(C)=C$.
--
--   Then there exists $f\in\mathbb R[x,y]$ such that:
--
--   1. $f$ is irreducible in $\mathbb C[x,y]$;
--   2. $f$ has total degree $d$;
--   3. $C$ is infinite;
--   4. $C$ is not a circle: there are no $c\in\mathbb C$ and real $R>0$ with $C=\{z:|z-c|=R\}$;
--   5. the full bound of Theorem 1 is attained:
--
--   $$|\mathrm{Sym}(C)|=2d.$$
--
--   This is the sharpness of the bound $|\mathrm{Sym}(C)|\le2d$ in Theorem 1, by a curve satisfying all the hypotheses of that theorem.
--
--   **Formalization Note**: the order is `Nat.card` of a subgroup of the group `ℂ ≃ᵢ ℂ` of isometric bijections; since its value is positive, finiteness is part of the conclusion.
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

theorem CurveSymmetry.paper_full_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = d ∧
      (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (isometrySetGroup (cartesianLocus f)) = 2 * d := by sorry
