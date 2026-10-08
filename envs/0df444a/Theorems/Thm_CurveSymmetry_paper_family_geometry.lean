-- Prove2me | Theorems.Thm_CurveSymmetry_paper_family_geometry
-- name    : CurveSymmetry.paper_family_geometry
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:45.729526+00:00
-- url     : https://prove2.me/theorems/80daeb2f-5e4b-4fa9-a66f-c5671ba18c82
-- title:
--   Theorem 2 (the extremal family): $C_{m,\alpha}$ is an infinite geometrically irreducible curve of degree $m+2$
-- statement:
--   Let $m\ge 2$ be an integer and let $\alpha\in\mathbb{C}$ be nonreal, that is, $\alpha\ne\bar\alpha$; no condition on $|\alpha|$ is imposed. Identify the real plane with $\mathbb{C}$ through $(x,y)\mapsto x+iy$ and let
--
--   $$C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}.$$
--
--   A real polynomial $f\in\mathbb{R}[x,y]$ has real zero set $Z(f)=\{z\in\mathbb{C} : f(\operatorname{Re}z,\operatorname{Im}z)=0\}$, and it is called geometrically irreducible if it is irreducible as an element of $\mathbb{C}[x,y]$.
--
--   Then there exists a real polynomial $f\in\mathbb{R}[x,y]$ with
--
--   $$Z(f)=C_{m,\alpha}$$
--
--   such that:
--
--   1. $f$ is geometrically irreducible;
--   2. $f$ has total degree $m+2$;
--   3. the set $C_{m,\alpha}$ is infinite.
--
--   This is the opening assertion of Theorem 2 of the note, that $C_{m,\alpha}$ is an infinite geometrically irreducible curve of degree $m+2$, including the quartic case $m=2$. The note states it for $|\alpha|=1$; here $\alpha$ is only assumed to be nonreal. Lemma 4 of the note contains the corresponding irreducibility and infinitude assertions.
--
--   **Formalization Note**: The curve is a subset of $\mathbb{C}$, its degree is the total degree of the real polynomial $f$, and geometric irreducibility is irreducibility of the image of $f$ under $\mathbb{R}[x,y]\to\mathbb{C}[x,y]$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Theorem 2, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/PaperFamilyGeometry.lean (C. Perassi)

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

theorem CurveSymmetry.paper_family_geometry {m : ℕ} (hm : 2 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = m + 2 ∧
      cartesianLocus f = extremalCurve m α ∧ (cartesianLocus f).Infinite := by sorry
