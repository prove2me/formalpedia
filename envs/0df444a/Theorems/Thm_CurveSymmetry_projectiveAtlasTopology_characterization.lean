-- Prove2me | Theorems.Thm_CurveSymmetry_projectiveAtlasTopology_characterization
-- name    : CurveSymmetry.projectiveAtlasTopology_characterization
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:13.334976+00:00
-- url     : https://prove2.me/theorems/1930a0b2-4608-457c-9216-5bf5c07f2029
-- title:
--   The atlas topology is the unique topology on $\mathbb P^1\times\mathbb P^1$ making the four charts open embeddings
-- statement:
--   Let $\mathbb P^1$ be the complex projective line, the set of lines through the origin of $\mathbb C^2$, with homogeneous coordinates $[x_0:x_1]$. Consider the four standard charts $\phi_i\colon\mathbb C^2\to\mathbb P^1\times\mathbb P^1$, $\phi_0(X,Y)=([X:1],[Y:1])$, $\phi_1(u,Y)=([1:u],[Y:1])$, $\phi_2(v,X)=([X:1],[1:v])$ and $\phi_3(u,v)=([1:u],[1:v])$, and give $\mathbb C^2$ its Zariski topology, whose closed sets are the common zero sets of families of polynomials in two variables. Let $\tau_{\mathrm{atlas}}$ be the atlas topology, the final topology of the four charts: a set $U\subseteq\mathbb P^1\times\mathbb P^1$ is open if and only if $\phi_i^{-1}(U)$ is Zariski open in $\mathbb C^2$ for $i=0,1,2,3$.
--
--   Then for every topology $\tau$ on $\mathbb P^1\times\mathbb P^1$,
--
--   $$\bigl(\phi_i\colon(\mathbb C^2,\text{Zariski})\to(\mathbb P^1\times\mathbb P^1,\tau)\ \text{is an open embedding for}\ i=0,1,2,3\bigr)\iff\tau=\tau_{\mathrm{atlas}}.$$
--
--   It characterizes the topology in which $V_\alpha$, the closure of the curve (6), is taken (the note introduces $V_\alpha$ before Lemma 4): the atlas topology is exactly the topology for which the four standard charts, with the classical Zariski topology on $\mathbb C^2$, are open embeddings.
--
--   **Formalization Note**: the characterization uses the four charts only; the atlas topology is not compared with the Zariski topology of $\mathbb P^1\times\mathbb P^1$ constructed as a scheme or projective spectrum. The Zariski topology on $\mathbb C^2$ is a local instance, induced from the prime spectrum of the polynomial ring through evaluation ideals.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 3, closure of equation (6), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/ProjectiveAtlasUniqueness.lean (C. Perassi)

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
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasUniqueness

theorem CurveSymmetry.projectiveAtlasTopology_characterization
    (t : TopologicalSpace (ProjectiveLine × ProjectiveLine)) :
    (∀ i, @Topology.IsOpenEmbedding _ _ affineZariskiTopology t (projectiveChart i)) ↔
      t = projectiveAtlasTopology := by sorry
