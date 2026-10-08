-- Prove2me | Theorems.Thm_CurveSymmetry_dvd_of_realLocus_subset
-- name    : CurveSymmetry.dvd_of_realLocus_subset
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:28.165534+00:00
-- url     : https://prove2.me/theorems/aa534efd-fd0f-4148-8741-51f39c22d57f
-- title:
--   If the infinite real locus of an irreducible $P$ lies in that of $Q$, then $P$ divides $Q$
-- statement:
--   Identify the Euclidean plane with $\mathbb C$ and use the complex coordinates $X=z$, $Y=\bar z$. For $P,Q\in\mathbb C[X,Y]$ let $C_P=\{z\in\mathbb C: P(z,\bar z)=0\}$ and $C_Q=\{z\in\mathbb C: Q(z,\bar z)=0\}$ be their real loci. Assume that $P$ is irreducible in $\mathbb C[X,Y]$, that $C_P$ is infinite, and that $C_P\subseteq C_Q$. Then
--
--   $$
--   P\mid Q\quad\text{in }\mathbb C[X,Y].
--   $$
--
--   This is the density step in the proof of Lemma 3, where an infinite real locus is Zariski dense in the irreducible complex curve. In the formalization it turns inclusions of real loci into polynomial identities, for instance to exclude translations, to show that a symmetry multiplies the equation by a constant, and to rule out the fixed line of a reflection as a component.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 3, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/Elimination.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.dvd_of_realLocus_subset {P Q : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) (hsub : realLocus P ⊆ realLocus Q) : P ∣ Q := by sorry
