-- Prove2me | Theorems.Thm_CurveSymmetry_paper_equality_classification
-- name    : CurveSymmetry.paper_equality_classification
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:43.741225+00:00
-- url     : https://prove2.me/theorems/b6b3c467-0245-455b-b996-429054d53809
-- title:
--   Theorem 1 (equality case): if $d\ge5$ and $|\mathrm{Sym}^+(C)|=2d-4$, a similarity maps $C$ onto some $C_{d-2,\alpha}$
-- statement:
--   Let $f\in\mathbb R[x,y]$ be irreducible in $\mathbb C[x,y]$ and of total degree $d\ge5$, and let $C=\{z\in\mathbb C: f(\operatorname{Re}z,\operatorname{Im}z)=0\}$ be its real zero set, identifying $(x,y)$ with $x+iy$. Assume that $C$ is infinite, that $C$ is not a circle (there are no $c\in\mathbb C$ and real $R>0$ with $C=\{z:|z-c|=R\}$), and that the group $\mathrm{Sym}^+(C)$ of orientation-preserving isometries $z\mapsto az+b$, $|a|=1$, mapping $C$ onto itself has exactly $2d-4$ elements. For an integer $m\ge0$ and $\alpha\in\mathbb C$ write $C_{m,\alpha}=\{w\in\mathbb C:\operatorname{Re}\bigl(w^m(|w|^2+\alpha)\bigr)=0\}$.
--
--   Then there exist $a,b,\alpha\in\mathbb C$ with $a\ne0$, $|\alpha|=1$ and $\alpha\notin\mathbb R$ such that the orientation-preserving similarity $z\mapsto az+b$ carries $C$ onto $C_{d-2,\alpha}$:
--   $$\{az+b: z\in C\}=C_{d-2,\alpha}.$$
--
--   This is the equality clause of Theorem 1: for $d\ge5$, a curve attaining the rotation bound $2d-4$ is, up to an orientation-preserving similarity, a curve of the family (1) with $m=d-2$.
--
--   **Formalization Note**: the curve is a subset of $\mathbb C$ and $\mathrm{Sym}^+(C)$ is a subgroup of the group `ℂ ≃ᵢ ℂ` of isometric bijections; its order is `Nat.card`, so the hypothesis, with $2d-4>0$, includes finiteness.
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

theorem CurveSymmetry.paper_equality_classification {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 5 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R)
    (hcard : Nat.card (directIsometryGroup (cartesianLocus f)) = 2 * f.totalDegree - 4) :
    ∃ a b α : ℂ, a ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧
      (fun z : ℂ => a * z + b) '' cartesianLocus f = extremalCurve (f.totalDegree - 2) α := by sorry
