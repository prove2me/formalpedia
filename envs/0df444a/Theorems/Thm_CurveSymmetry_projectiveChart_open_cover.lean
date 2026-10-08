-- Prove2me | Theorems.Thm_CurveSymmetry_projectiveChart_open_cover
-- name    : CurveSymmetry.projectiveChart_open_cover
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:47.157043+00:00
-- url     : https://prove2.me/theorems/77184001-c08b-4b17-a228-b3da0b6aa218
-- title:
--   The four standard charts cover $\mathbb P^1\times\mathbb P^1$
-- statement:
--   Let $\mathbb P^1$ be the complex projective line, the set of lines through the origin of $\mathbb C^2$, with homogeneous coordinates $[x_0:x_1]$. Consider the four standard charts $\phi_i\colon\mathbb C^2\to\mathbb P^1\times\mathbb P^1$, $\phi_0(X,Y)=([X:1],[Y:1])$, $\phi_1(u,Y)=([1:u],[Y:1])$, $\phi_2(v,X)=([X:1],[1:v])$ and $\phi_3(u,v)=([1:u],[1:v])$.
--
--   Then every point of $\mathbb P^1\times\mathbb P^1$ lies in the image of one of them:
--
--   $$\phi_0(\mathbb C^2)\cup\phi_1(\mathbb C^2)\cup\phi_2(\mathbb C^2)\cup\phi_3(\mathbb C^2)=\mathbb P^1\times\mathbb P^1.$$
--
--   This is an equality of sets; no topology enters.
--
--   Together with the openness of the chart images, it makes the four charts an open cover of $\mathbb P^1\times\mathbb P^1$ for the atlas topology, in which $V_\alpha$, the closure of the curve (6), is taken; the note introduces $V_\alpha$ before Lemma 4.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 3, closure of equation (6), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/ProjectiveAtlasOpenCover.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Constructions

open CurveSymmetry
set_option autoImplicit false
open OnePoint
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasOpenCover
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasOpenCover

theorem CurveSymmetry.projectiveChart_open_cover :
    (⋃ i, Set.range (projectiveChart i)) = Set.univ := by sorry
