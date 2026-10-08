-- Prove2me | Theorems.Thm_CurveSymmetry_spectrum_vanishingIdeal_image
-- name    : CurveSymmetry.spectrum_vanishingIdeal_image
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:46:10.573255+00:00
-- url     : https://prove2.me/theorems/14ecd045-bd08-45a7-9430-42af90bc2876
-- title:
--   Vanishing ideals of sets of complex points agree in $\mathbb C[X,Y]$ and in $\operatorname{Spec}\mathbb C[X,Y]$
-- statement:
--   For $v=(v_0,v_1)\in\mathbb C^2$ let $\mathfrak m_v=\{Q\in\mathbb C[X,Y]:Q(v)=0\}$ be the kernel of evaluation at $v$, that is, the maximal ideal $(X-v_0,\,Y-v_1)$, regarded as a point of the prime spectrum $\operatorname{Spec}\mathbb C[X,Y]$. The vanishing ideal of a set of prime ideals is their intersection, the whole ring for the empty set.
--
--   Then for every subset $S\subseteq\mathbb C^2$
--
--   $$
--   \bigcap_{v\in S}\mathfrak m_v=\{Q\in\mathbb C[X,Y]:\ Q(v)=0\ \text{for all}\ v\in S\}.
--   $$
--
--   It translates between the classical vanishing ideal of a set of complex points and the vanishing ideal, in $\operatorname{Spec}\mathbb C[X,Y]$, of the corresponding closed points. The formalization uses it to compute Zariski closures in the prime spectrum from classical vanishing ideals, for instance the closure of the real points of the curve (6).
--
--   **Formalization Note**: the left side is `PrimeSpectrum.vanishingIdeal` of the image of $S$ under $v\mapsto\mathfrak m_v$, and the right side is `MvPolynomial.vanishingIdeal ℂ S`.
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

theorem CurveSymmetry.spectrum_vanishingIdeal_image (S : Set (Fin 2 → ℂ)) :
    PrimeSpectrum.vanishingIdeal (affineSpectrumPoint '' S) = vanishingIdeal ℂ S := by sorry
