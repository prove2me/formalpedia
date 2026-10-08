-- Prove2me | Theorems.Thm_CurveSymmetry_paper_family_converse
-- name    : CurveSymmetry.paper_family_converse
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:52.855051+00:00
-- url     : https://prove2.me/theorems/d442f6d8-a254-43cd-80b5-8e8158179552
-- title:
--   Theorem 1 (converse of the equality case): $|\mathrm{Sym}^+(C_{m,\alpha})|=2m$ for $m\ge3$ and every nonreal $\alpha$
-- statement:
--   Let $m\ge3$ be an integer and let $\alpha\in\mathbb C$ with $\alpha\notin\mathbb R$; no condition is imposed on $|\alpha|$. Let $C_{m,\alpha}=\{z\in\mathbb C:\operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$ as in equation (1), and let $\mathrm{Sym}^+(C_{m,\alpha})$ be the group of orientation-preserving Euclidean isometries $z\mapsto az+b$, $|a|=1$, mapping $C_{m,\alpha}$ onto itself.
--
--   Then there is a polynomial $f\in\mathbb R[x,y]$ with the following properties:
--
--   1. $f$ is irreducible in $\mathbb C[x,y]$ and has total degree $m+2$;
--   2. the real zero set of $f$ is $C_{m,\alpha}$, that is, $\{z\in\mathbb C: f(\operatorname{Re}z,\operatorname{Im}z)=0\}=C_{m,\alpha}$;
--   3. $C_{m,\alpha}$ is infinite;
--   4. $C_{m,\alpha}$ is not a circle: there are no $c\in\mathbb C$ and real $R>0$ with $C_{m,\alpha}=\{z:|z-c|=R\}$;
--   5. the group $\mathrm{Sym}^+(C_{m,\alpha})$ has order $2m=2\deg f-4$:
--
--   $$|\mathrm{Sym}^+(C_{m,\alpha})|=2m.$$
--
--   This is the converse in Theorem 1: every curve of the family (1) with $m\ge3$ satisfies the hypotheses of that theorem in degree $d=m+2$ and attains the rotation bound $2d-4$. The statement requires only $\alpha\notin\mathbb R$, while the family in the note also has $|\alpha|=1$.
--
--   **Formalization Note**: the curve is a subset of $\mathbb C$ and $\mathrm{Sym}^+(C_{m,\alpha})$ is a subgroup of the group `ℂ ≃ᵢ ℂ` of isometric bijections; its order is `Nat.card`, so with $2m>0$ finiteness is part of the conclusion.
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

theorem CurveSymmetry.paper_family_converse {m : ℕ} (hm : 3 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = m + 2 ∧
      cartesianLocus f = extremalCurve m α ∧ (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (directIsometryGroup (cartesianLocus f)) = 2 * m := by sorry
