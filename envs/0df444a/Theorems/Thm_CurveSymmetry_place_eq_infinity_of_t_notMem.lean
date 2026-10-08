-- Prove2me | Theorems.Thm_CurveSymmetry_place_eq_infinity_of_t_notMem
-- name    : CurveSymmetry.place_eq_infinity_of_t_notMem
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:45.239051+00:00
-- url     : https://prove2.me/theorems/78680188-2f7a-4019-806e-c4e8923d8914
-- title:
--   A place of $\mathbb C(t)[W]/(W^2-h_\alpha)$ containing $\mathbb C$ but not $t$ is the place at infinity
-- statement:
--   Let $m\ge 1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$ (that is, $\alpha$ is not real), and let $h_\alpha(t)=-t\,(t^m+1)\,(\alpha t^m+\bar\alpha)\in\mathbb C[t]$. Let $L_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$, with $w$ the class of $W$. In the coordinate $s=1/t$ the double cover becomes the one with parameter $\bar\alpha$: let $L_{\bar\alpha}=\mathbb C(s)[W']/(W'^2-h_{\bar\alpha}(s))$, with $w'$ the class of $W'$, and let $\psi\colon L_\alpha\to L_{\bar\alpha}$ be the ring homomorphism with $\psi(r(t))=r(1/s)$ for $r\in\mathbb C(t)$ and $\psi(w)=w'/s^{m+1}$. Let $\mathcal O'_{0,0}\subseteq L_{\bar\alpha}$ be the local ring of the point $(s,w')=(0,0)$ of $w'^2=h_{\bar\alpha}(s)$, that is, the localization of $\mathbb C[s][W']/(W'^2-h_{\bar\alpha}(s))$ at the kernel of the evaluation $s\mapsto0$, $W'\mapsto0$. The place at infinity of $L_\alpha$ is $\mathcal O_\infty=\psi^{-1}(\mathcal O'_{0,0})$.
--
--   Let $\mathcal O$ be a valuation subring of $L_\alpha$ with $\mathcal O\ne L_\alpha$ that contains the constants $\mathbb C$ and does not contain $t$. Then
--
--   $$
--   \mathcal O=\mathcal O_\infty.
--   $$
--
--   This is the uniqueness of the place over $t=\infty$ of the double cover (7). With the places over the finite $t$-line, it completes the list of places of the function field of $V_\alpha$ used for the genus in Lemma 4 and for Remark 5.
--
--   **Formalization Note**: $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instances.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Lemma 4, equation (7), p. 3, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/QuadraticInfinity.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

theorem CurveSymmetry.place_eq_infinity_of_t_notMem (O : ValuationSubring (QuadField (familyH m α)))
    (htop : O ≠ ⊤) (hconst : ∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ O)
    (ht : algebraMap ℂ[X] (QuadField (familyH m α)) X ∉ O) :
    O = familyInfinityPlace m α := by sorry
