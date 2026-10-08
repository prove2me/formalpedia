-- Prove2me | Theorems.Thm_CurveSymmetry_real_diagonal_algebraic_closure
-- name    : CurveSymmetry.real_diagonal_algebraic_closure
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:11.665151+00:00
-- url     : https://prove2.me/theorems/ae2b2e63-d88d-4d55-a8ab-dd953fb7c678
-- title:
--   Equations vanishing on the infinitely many real points of an irreducible $P$ cut out exactly the curve $P=0$
-- statement:
--   Let $P\in\mathbb C[X,Y]$ be irreducible. Writing points of the real plane as $z\in\mathbb C$, the real locus of $P$ in the coordinates $X=z$, $Y=\bar z$ is $Z(P)=\{z\in\mathbb C:P(z,\bar z)=0\}$. Let $\Delta_P=\{(z,\bar z):z\in Z(P)\}\subseteq\mathbb C^2$ be its image under $z\mapsto(z,\bar z)$, and let $I(\Delta_P)=\{Q\in\mathbb C[X,Y]:Q(v)=0\ \text{for all}\ v\in\Delta_P\}$ be the ideal of the polynomials vanishing on $\Delta_P$.
--
--   If $Z(P)$ is infinite, then
--
--   $$
--   \{v\in\mathbb C^2:\ Q(v)=0\ \text{for all}\ Q\in I(\Delta_P)\}=\{v\in\mathbb C^2:\ P(v)=0\}.
--   $$
--
--   In the classical Zariski topology of $\mathbb C^2$ this says that the closure of the real points $\Delta_P$ is the whole complex curve $P=0$: the Zariski density of an infinite real locus that the note invokes in the proofs of Lemma 3 and Theorem 2. For the polynomial $P_\alpha$ of equation (6), with $|\alpha|=1$ and $\alpha\notin\mathbb R$ as in Lemma 4, the points $(z,\bar z)$ with $z\in C_{m,\alpha}$ are therefore Zariski dense in the complex affine curve $P_\alpha=0$, the affine part of the curve $V_\alpha\subset\mathbb P^1\times\mathbb P^1$ obtained by closing (6).
--
--   **Formalization Note**: the left side is Mathlib's `MvPolynomial.zeroLocus ℂ` of `MvPolynomial.vanishingIdeal ℂ`, with irreducibility taken in `MvPolynomial (Fin 2) ℂ`.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 3, closure of equation (6), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/AffineClosure.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
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

theorem CurveSymmetry.real_diagonal_algebraic_closure {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) :
    zeroLocus ℂ (vanishingIdeal ℂ (affineRealDiagonal P)) =
      {v : Fin 2 → ℂ | eval v P = 0} := by sorry
