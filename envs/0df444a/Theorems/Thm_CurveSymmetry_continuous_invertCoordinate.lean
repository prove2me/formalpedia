-- Prove2me | Theorems.Thm_CurveSymmetry_continuous_invertCoordinate
-- name    : CurveSymmetry.continuous_invertCoordinate
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:49.939366+00:00
-- url     : https://prove2.me/theorems/e0ae1e63-182d-420a-80d4-c1519a026f0c
-- title:
--   Inverting one coordinate is continuous for the Zariski topology where that coordinate is nonzero
-- statement:
--   Give $\mathbb C^2$ its Zariski topology, whose closed sets are the common zero sets of families of polynomials in $\mathbb C[X_0,X_1]$. Fix an index $i\in\{0,1\}$, let $D_i=\{v=(v_0,v_1)\in\mathbb C^2: v_i\ne0\}$ carry the subspace topology, and let $\iota_i\colon D_i\to\mathbb C^2$ invert the coordinate $v_i$ and keep the other one:
--
--   $$\iota_0(v_0,v_1)=(v_0^{-1},v_1),\qquad\iota_1(v_0,v_1)=(v_0,v_1^{-1}).$$
--
--   Then $\iota_i$ is continuous from $D_i$ to $\mathbb C^2$, both with the Zariski topology.
--
--   The transition maps between the four standard charts of $\mathbb P^1\times\mathbb P^1$ invert one coordinate where it is nonzero. This continuity is used to show that the charts are open embeddings for the atlas topology on $\mathbb P^1\times\mathbb P^1$, the setting in which the singular points of $V_\alpha$, the closure of the curve (6), are computed for Lemma 4.
--
--   **Formalization Note**: the Zariski topology on $\mathbb C^2$ is induced from the prime spectrum of $\mathbb C[X_0,X_1]$ by sending a point to its evaluation ideal; it is a local instance and does not replace the Euclidean topology of $\mathbb C^2$ elsewhere.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Lemma 4 (p. 3), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/InversionContinuity.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_inversionContinuity

theorem CurveSymmetry.continuous_invertCoordinate (i : Fin 2) :
    Continuous (fun v : CoordinateNonzero i => invertCoordinate i v.val) := by sorry
