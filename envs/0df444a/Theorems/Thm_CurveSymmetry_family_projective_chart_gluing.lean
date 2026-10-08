-- Prove2me | Theorems.Thm_CurveSymmetry_family_projective_chart_gluing
-- name    : CurveSymmetry.family_projective_chart_gluing
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:36.83837+00:00
-- url     : https://prove2.me/theorems/935fb9c1-e80b-45f2-b7e9-7c66dee3957b
-- title:
--   Chart gluing: a set closed in all four charts and containing the affine curve $P_\alpha=0$ contains $V_\alpha$
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha\in\mathbb C$ be arbitrary. Let $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ be the polynomial of equation (6), and let $V_\alpha\subseteq\mathbb P^1\times\mathbb P^1$ be the zero locus of its bihomogenization of bidegree $(m+1,m+1)$ in homogeneous coordinates $([x_0:x_1],[y_0:y_1])$,
--
--   $$F_\alpha(x,y)=\alpha x_0^mx_1y_1^{m+1}+x_0^{m+1}y_0y_1^m+\bar\alpha x_1^{m+1}y_0^my_1+x_0x_1^my_0^{m+1},$$
--
--   so that $F_\alpha((X,1),(Y,1))=P_\alpha(X,Y)$. Consider the four standard charts $\phi_i\colon\mathbb C^2\to\mathbb P^1\times\mathbb P^1$, $\phi_0(X,Y)=([X:1],[Y:1])$, $\phi_1(u,Y)=([1:u],[Y:1])$, $\phi_2(v,X)=([X:1],[1:v])$ and $\phi_3(u,v)=([1:u],[1:v])$, and give $\mathbb C^2$ its Zariski topology, whose closed sets are the common zero sets of families of polynomials in two variables. Let $S\subseteq\mathbb P^1\times\mathbb P^1$ be a set such that $\phi_i^{-1}(S)$ is Zariski closed in $\mathbb C^2$ for each $i=0,1,2,3$.
--
--   Then, if $S$ contains the affine curve in the chart $\phi_0$, it contains all of $V_\alpha$:
--
--   $$\phi_0\bigl(\{(X,Y)\in\mathbb C^2: P_\alpha(X,Y)=0\}\bigr)\subseteq S\ \Longrightarrow\ V_\alpha\subseteq S.$$
--
--   This is the gluing step in identifying $V_\alpha$ with the closure of the affine curve (6) in $\mathbb P^1\times\mathbb P^1$, the curve whose singular points and genus Lemma 4 describes: a set that is closed in every chart and contains the affine curve already contains all of $V_\alpha$, boundary points included.
--
--   **Formalization Note**: no topology on $\mathbb P^1\times\mathbb P^1$ is used; closedness of $S$ is required chart by chart, for the Zariski topology on $\mathbb C^2$ induced from the prime spectrum through evaluation ideals (a local instance). $V_\alpha$ is defined by evaluating $F_\alpha$ at chosen representatives of the two points, which does not depend on the choice by bihomogeneity.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Lemma 4 (p. 3), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/ProjectiveClosureGluing.lean (C. Perassi)

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

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveClosureGluing

theorem CurveSymmetry.family_projective_chart_gluing {m : ℕ} (hm : 0 < m) (α : ℂ)
    (S : Set (ProjectiveLine × ProjectiveLine)) (hs : ClosedInProjectiveCharts S)
    (hA : affineProjectiveChart '' {v : Fin 2 → ℂ | eval v (familyPolynomial m α) = 0} ⊆ S) :
    familyProjectiveCurve m α ⊆ S := by sorry
