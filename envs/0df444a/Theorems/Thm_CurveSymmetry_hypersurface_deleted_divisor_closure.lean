-- Prove2me | Theorems.Thm_CurveSymmetry_hypersurface_deleted_divisor_closure
-- name    : CurveSymmetry.hypersurface_deleted_divisor_closure
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:35.872358+00:00
-- url     : https://prove2.me/theorems/e5e65f2c-5c4b-4e20-9363-8a0c8e7eb84d
-- title:
--   Removing a divisor that contains no component of $F=0$ does not change the Zariski closure of $V(F)$
-- statement:
--   Let $F,u\in\mathbb C[X,Y]$ with $F\ne0$, and assume that no irreducible factor of $F$ divides $u$: for every irreducible $q\in\mathbb C[X,Y]$ with $q\mid F$ one has $q\nmid u$. In the prime spectrum $\operatorname{Spec}\mathbb C[X,Y]$ with its Zariski topology put $V(F)=\{\mathfrak p:F\in\mathfrak p\}$ and $D(u)=\{\mathfrak p:u\notin\mathfrak p\}$. Then
--
--   $$
--   \overline{V(F)\cap D(u)}=V(F).
--   $$
--
--   Neither $F$ nor $u$ needs to be irreducible. In the formalization $u$ is a chart coordinate, such as $u=1/X$ in a boundary chart of $\mathbb P^1\times\mathbb P^1$: the part of the chart curve where $u\ne0$, which lies over the affine plane, is dense in the whole chart curve. This is how the boundary points are shown to lie in the closure of the curve (6) in $\mathbb P^1\times\mathbb P^1$.
--
--   **Formalization Note**: $V(F)$ is `PrimeSpectrum.zeroLocus {F}` in `PrimeSpectrum (MvPolynomial (Fin 2) ℂ)`, whose topology is Mathlib's Zariski topology.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Section 3, closure of equation (6), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/MixedCornerClosure.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
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

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.hypersurface_deleted_divisor_closure (F u : BPoly) (hF0 : F ≠ 0)
    (havoid : ∀ q : BPoly, Irreducible q → q ∣ F → ¬ q ∣ u) :
    closure (PrimeSpectrum.zeroLocus ({F} : Set BPoly) ∩
      {p : PrimeSpectrum BPoly | u ∉ p.asIdeal}) =
      PrimeSpectrum.zeroLocus ({F} : Set BPoly) := by sorry
