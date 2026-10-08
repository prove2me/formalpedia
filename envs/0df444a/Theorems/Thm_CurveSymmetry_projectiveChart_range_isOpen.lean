-- Prove2me | Theorems.Thm_CurveSymmetry_projectiveChart_range_isOpen
-- name    : CurveSymmetry.projectiveChart_range_isOpen
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:51.908986+00:00
-- url     : https://prove2.me/theorems/2ed4d290-5401-4adc-9f93-47eaace459f8
-- title:
--   Each of the four standard charts has open image in $\mathbb P^1\times\mathbb P^1$ for the atlas topology
-- statement:
--   Let $\mathbb P^1$ be the complex projective line, the set of lines through the origin of $\mathbb C^2$, with homogeneous coordinates $[x_0:x_1]$. Consider the four standard charts $\phi_i\colon\mathbb C^2\to\mathbb P^1\times\mathbb P^1$, $\phi_0(X,Y)=([X:1],[Y:1])$, $\phi_1(u,Y)=([1:u],[Y:1])$, $\phi_2(v,X)=([X:1],[1:v])$ and $\phi_3(u,v)=([1:u],[1:v])$. Give $\mathbb C^2$ its Zariski topology, whose closed sets are the common zero sets of families of polynomials in two variables, and $\mathbb P^1\times\mathbb P^1$ the atlas topology, the final topology of the four charts: a set $U\subseteq\mathbb P^1\times\mathbb P^1$ is open if and only if $\phi_i^{-1}(U)$ is Zariski open in $\mathbb C^2$ for $i=0,1,2,3$.
--
--   Then for every $j\in\{0,1,2,3\}$ the image of the chart $\phi_j$ is open:
--
--   $$\phi_j(\mathbb C^2)\ \text{is open in}\ \mathbb P^1\times\mathbb P^1.$$
--
--   This is part of the construction of the topology on $\mathbb P^1\times\mathbb P^1$ in which $V_\alpha$, the closure of the curve (6), is taken; the note introduces $V_\alpha$ before Lemma 4.
--
--   **Formalization Note**: the atlas topology is the final topology of the map from the disjoint union of four copies of $\mathbb C^2$ given by the four charts; it is not the product topology. The Zariski topology on $\mathbb C^2$ is induced from the prime spectrum of the polynomial ring through evaluation ideals. Both topologies are local instances.
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

theorem CurveSymmetry.projectiveChart_range_isOpen (j : Fin 4) : IsOpen (Set.range (projectiveChart j)) := by sorry
