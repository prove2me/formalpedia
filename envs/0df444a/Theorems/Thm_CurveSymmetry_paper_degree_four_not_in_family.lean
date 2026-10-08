-- Prove2me | Theorems.Thm_CurveSymmetry_paper_degree_four_not_in_family
-- name    : CurveSymmetry.paper_degree_four_not_in_family
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:13.960623+00:00
-- url     : https://prove2.me/theorems/3bb781d6-54ef-411b-9e00-ad261d03940d
-- title:
--   Remark 5 (degree four): $\operatorname{Re}(z^4)=1$ has four rotations and is not similar to any $C_{2,\alpha}$
-- statement:
--   Identify the Euclidean plane with $\mathbb C$. For $S\subseteq\mathbb C$ let $\mathrm{Sym}^+(S)$ be the group of orientation-preserving Euclidean isometries $T(z)=az+b$ ($a,b\in\mathbb C$, $|a|=1$) with $T(S)=S$. Let $C_4=\{z\in\mathbb C:\operatorname{Re}(z^4)=1\}$ and, for $\alpha\in\mathbb C$, let $C_{2,\alpha}=\{z\in\mathbb C:\operatorname{Re}\bigl(z^2(|z|^2+\alpha)\bigr)=0\}$, the set of equation (1) of the note with $m=2$ (where the note takes $|\alpha|=1$ and $\alpha\notin\mathbb R$). For $a,b\in\mathbb C$ and $S\subseteq\mathbb C$ write $aS+b=\{az+b:z\in S\}$ and $a\overline S+b=\{a\bar z+b:z\in S\}$.
--
--   Then:
--
--   1. $\mathrm{Sym}^+(C_4)$ has exactly four elements;
--   2. no similarity of the plane, direct ($z\mapsto az+b$) or orientation-reversing ($z\mapsto a\bar z+b$), with $a\ne0$, carries $C_4$ onto a set $C_{2,\alpha}$ with $\alpha$ nonreal.
--
--   In formulas:
--   $$|\mathrm{Sym}^+(C_4)|=4\qquad\text{and}\qquad\nexists\,a,b,\alpha\in\mathbb C:\ a\ne0,\ \alpha\ne\bar\alpha,\ \bigl(aC_4+b=C_{2,\alpha}\ \text{or}\ a\overline{C_4}+b=C_{2,\alpha}\bigr).$$
--
--   This is the degree-four example of Remark 5 of the note: $\operatorname{Re}(z^4)=1$ attains the rotation bound $\max\{d,2d-4\}=4$ of Theorem 1 with $d=4$, yet it is not in the $m=2$ family; Remark 5 uses it to show that the restriction $d\ge5$ in the equality clause of Theorem 1 is necessary. Here the parameter $\alpha$ is only required to be nonreal.
--
--   **Formalization Note**: $\mathrm{Sym}^+(S)$ is a subgroup of the isometry group `ℂ ≃ᵢ ℂ`, and its size is `Nat.card`, which is $0$ for an infinite group; the value $4$ thus includes finiteness.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/PaperRemarks.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
import Definitions.Def_CurveSymmetry_11_KummerLocal
import Definitions.Def_CurveSymmetry_12_FermatGenus
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
import Mathlib.LinearAlgebra.Dimension.Finrank
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
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

open CurveSymmetry
set_option autoImplicit false

theorem CurveSymmetry.paper_degree_four_not_in_family :
    Nat.card (directIsometryGroup {z : ℂ | (z ^ 4).re = 1}) = 4 ∧
      ¬ ∃ a b α : ℂ, a ≠ 0 ∧ α ≠ star α ∧
        ((fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α ∨
          (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α) := by sorry
