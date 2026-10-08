-- Prove2me | Theorems.Thm_CurveSymmetry_family_kaehler_dt
-- name    : CurveSymmetry.family_kaehler_dt
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:33.680983+00:00
-- url     : https://prove2.me/theorems/fdd11878-55ac-4d57-926e-214441fe2ad4
-- title:
--   The differentials of $\mathbb C(t)[W]/(W^2-h_\alpha)$ form a one-dimensional space spanned by $dt$
-- statement:
--   Let $m\ge 1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$ (that is, $\alpha$ is not real), and let $h_\alpha(t)=-t\,(t^m+1)\,(\alpha t^m+\bar\alpha)\in\mathbb C[t]$. Let $L_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$, and let $\Omega_{L_\alpha/\mathbb C}$ be the module of Kähler differentials of $L_\alpha$ over $\mathbb C$, with universal derivation $d$. Then
--
--   $$
--   \dim_{L_\alpha}\Omega_{L_\alpha/\mathbb C}=1\qquad\text{and}\qquad\Omega_{L_\alpha/\mathbb C}=L_\alpha\,dt.
--   $$
--
--   $L_\alpha$ is the function field of $V_\alpha$ in the form of the double cover (7). In the formalization the genus $m$ in Lemma 4 is computed from an explicit basis $t^i\,dt/w$, $0\le i<m$, of the holomorphic differentials, and this statement provides the one-dimensional space in which they live; orders of vanishing and the genus are not part of it.
--
--   **Formalization Note**: $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instances.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuadraticDifferentials.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_08_Differentials
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
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

theorem CurveSymmetry.family_kaehler_dt :
    Module.finrank (QuadField (familyH m α)) Ω[QuadField (familyH m α)⁄ℂ] = 1 ∧
      Submodule.span (QuadField (familyH m α))
          {KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α))} = ⊤ := by sorry
