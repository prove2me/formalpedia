-- Prove2me | Theorems.Thm_CurveSymmetry_familyProjectiveCurve_isIrreducible
-- name    : CurveSymmetry.familyProjectiveCurve_isIrreducible
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:24.549931+00:00
-- url     : https://prove2.me/theorems/a6538f45-7ac5-4ddf-bee0-d5ad1cc31ab8
-- title:
--   For nonreal $\alpha$, the curve $V_\alpha\subset\mathbb P^1\times\mathbb P^1$ is irreducible in the atlas topology
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$, that is $\alpha\notin\mathbb R$ (no condition on $|\alpha|$). On $\mathbb P^1\times\mathbb P^1$, with homogeneous coordinates $([x_0:x_1],[y_0:y_1])$, let
--
--   $$V_\alpha=\bigl\{([x_0:x_1],[y_0:y_1])\ :\ \alpha x_0^mx_1y_1^{m+1}+x_0^{m+1}y_0y_1^m+\bar\alpha x_1^{m+1}y_0^my_1+x_0x_1^my_0^{m+1}=0\bigr\},$$
--
--   the zero locus of the bihomogenization of bidegree $(m+1,m+1)$ of the polynomial $P_\alpha(X,Y)=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ of equation (6). Give $\mathbb P^1\times\mathbb P^1$ the atlas topology: for the four standard charts $\phi_0(X,Y)=([X:1],[Y:1])$, $\phi_1(u,Y)=([1:u],[Y:1])$, $\phi_2(v,X)=([X:1],[1:v])$ and $\phi_3(u,v)=([1:u],[1:v])$ from $\mathbb C^2$, a set $U$ is open if and only if every $\phi_i^{-1}(U)$ is open in the Zariski topology of $\mathbb C^2$.
--
--   Then $V_\alpha$ is irreducible: it is nonempty, and whenever $V_\alpha\subseteq A\cup B$ with $A,B$ closed, $V_\alpha\subseteq A$ or $V_\alpha\subseteq B$.
--
--   This concerns $V_\alpha$, the compactification of the curve (6) in $\mathbb P^1\times\mathbb P^1$ that the note introduces before Lemma 4: the whole compactified curve, boundary points included, is irreducible in the topology for which the four standard charts, with the Zariski topology on $\mathbb C^2$, are open embeddings.
--
--   **Formalization Note**: $V_\alpha$ is defined by evaluating the bihomogeneous polynomial at chosen representatives of the two points, which does not depend on the choice. The atlas topology and the Zariski topology on $\mathbb C^2$ (induced from the prime spectrum through evaluation ideals) are local instances.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 3, closure of equation (6), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/ProjectiveCurveIrreducibility.lean (C. Perassi)

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
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveCurveIrreducibility
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveCurveIrreducibility

theorem CurveSymmetry.familyProjectiveCurve_isIrreducible {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) : IsIrreducible (familyProjectiveCurve m α) := by sorry
