-- Prove2me | Theorems.Thm_CurveSymmetry_projectiveChart_isOpenEmbedding
-- name    : CurveSymmetry.projectiveChart_isOpenEmbedding
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:45.737874+00:00
-- url     : https://prove2.me/theorems/f452d97d-ec27-4987-9a15-0a483ce6212b
-- title:
--   The four standard charts are open embeddings into $\mathbb P^1\times\mathbb P^1$ with the atlas topology
-- statement:
--   Let $\mathbb P^1$ be the complex projective line, the set of lines through the origin of $\mathbb C^2$, with homogeneous coordinates $[x_0:x_1]$. Consider the four standard charts $\phi_i\colon\mathbb C^2\to\mathbb P^1\times\mathbb P^1$, $\phi_0(X,Y)=([X:1],[Y:1])$, $\phi_1(u,Y)=([1:u],[Y:1])$, $\phi_2(v,X)=([X:1],[1:v])$ and $\phi_3(u,v)=([1:u],[1:v])$. Give $\mathbb C^2$ its Zariski topology, whose closed sets are the common zero sets of families of polynomials in two variables, and $\mathbb P^1\times\mathbb P^1$ the atlas topology, the final topology of the four charts: a set $U\subseteq\mathbb P^1\times\mathbb P^1$ is open if and only if $\phi_i^{-1}(U)$ is Zariski open in $\mathbb C^2$ for $i=0,1,2,3$.
--
--   Then each chart is an open embedding: for every $i\in\{0,1,2,3\}$,
--
--   $$\phi_i\colon\mathbb C^2\to\mathbb P^1\times\mathbb P^1\ \text{is a homeomorphism onto the open subset}\ \phi_i(\mathbb C^2).$$
--
--   Singular points, multiplicities and tangent cones of $V_\alpha$, the closure of the curve (6), are computed in these four charts with the classical Zariski topology; this result makes each chart a topological coordinate system for that purpose and is used for Lemma 4. It also gives one direction of the characterization of the atlas topology as the unique topology with this property.
--
--   **Formalization Note**: the atlas topology is the final topology of the map from the disjoint union of four copies of $\mathbb C^2$ given by the four charts; it is not the product topology. The Zariski topology on $\mathbb C^2$ is induced from the prime spectrum of the polynomial ring through evaluation ideals. Both topologies are local instances.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Lemma 4 (p. 3), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/ProjectiveAtlasEmbeddings.lean (C. Perassi)

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
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings

theorem CurveSymmetry.projectiveChart_isOpenEmbedding (i : Fin 4) :
    Topology.IsOpenEmbedding (projectiveChart i) := by sorry
