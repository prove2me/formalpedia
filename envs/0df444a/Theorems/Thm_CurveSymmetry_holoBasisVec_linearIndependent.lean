-- Prove2me | Theorems.Thm_CurveSymmetry_holoBasisVec_linearIndependent
-- name    : CurveSymmetry.holoBasisVec_linearIndependent
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:55.436582+00:00
-- url     : https://prove2.me/theorems/c7000e98-6a61-4624-b983-c9c1414d998e
-- title:
--   The differentials $t^i\,dt/w$, $0\le i<m$, of $w^2=-t(t^m+1)(\alpha t^m+\bar\alpha)$ are linearly independent
-- statement:
--   Let $m\ge1$ be an integer and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$. Put $h_\alpha(t)=-t(t^m+1)(\alpha t^m+\bar\alpha)\in\mathbb C[t]$ and let $K_\alpha=\mathbb C(t)[W]/(W^2-h_\alpha(t))$, with $w$ the class of $W$, so that $w^2=h_\alpha(t)$; this is the function field of the double cover of the $t$-line in equation (7) of the note, written with $w=t(t^m+1)Y$. Let $\Omega_{K_\alpha/\mathbb C}$ be its module of Kähler differentials, with universal derivation $d$.
--
--   Then the $m$ differentials $t^i\,dt/w$, $0\le i\le m-1$, are linearly independent over $\mathbb C$ in $\Omega_{K_\alpha/\mathbb C}$: for $c_0,\dots,c_{m-1}\in\mathbb C$,
--
--   $$\sum_{i=0}^{m-1}c_i\,\frac{t^i\,dt}{w}=0\ \Longrightarrow\ c_0=c_1=\dots=c_{m-1}=0 .$$
--
--   Together with the facts that these differentials are holomorphic and span the holomorphic differentials of $K_\alpha$, this makes them a basis of that space, which gives the genus $m$ in Lemma 4 (genus two for $m=2$ in Remark 5).
--
--   **Formalization Note**: the hypotheses $m>0$ and $\alpha\ne\bar\alpha$ are `Fact` instances; $|\alpha|=1$ is not assumed.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Lemma 4, pp. 3-4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/HolomorphicBasis.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
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
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

theorem CurveSymmetry.holoBasisVec_linearIndependent :
    LinearIndependent ℂ (fun i : Fin m => holoBasisVec m α i) := by sorry
