-- Prove2me | Theorems.Thm_CurveSymmetry_paper_degree_four_genus
-- name    : CurveSymmetry.paper_degree_four_genus
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:14.549254+00:00
-- url     : https://prove2.me/theorems/ebeeadcd-3d6d-4d6d-a2a0-d65a8416ea19
-- title:
--   Remark 5: four rotations of $\operatorname{Re}(z^4)=1$, genera three versus two, no similarity to $C_{2,\alpha}$
-- statement:
--   Identify the Euclidean plane with $\mathbb C$. For $S\subseteq\mathbb C$ let $\mathrm{Sym}^+(S)$ be the group of orientation-preserving Euclidean isometries $T(z)=az+b$ ($a,b\in\mathbb C$, $|a|=1$) with $T(S)=S$. Let $C_4=\{z\in\mathbb C:\operatorname{Re}(z^4)=1\}$ and, for $\alpha\in\mathbb C$, let $C_{2,\alpha}=\{z\in\mathbb C:\operatorname{Re}\bigl(z^2(|z|^2+\alpha)\bigr)=0\}$, the set of equation (1) of the note with $m=2$ (where the note takes $|\alpha|=1$ and $\alpha\notin\mathbb R$). For $a,b\in\mathbb C$ and $S\subseteq\mathbb C$ write $aS+b=\{az+b:z\in S\}$ and $a\overline S+b=\{a\bar z+b:z\in S\}$.
--
--   Let $K_4=\operatorname{Frac}\bigl(\mathbb C[X,Y]/(X^4+Y^4-2)\bigr)$, the function field of the complexification $X^4+Y^4=2$ of $C_4$ in the coordinates $X=z$, $Y=\bar z$. For $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$ let $P_\alpha=X^2(\alpha+XY)+Y^2(\bar\alpha+XY)$, the polynomial of equation (6) of the note with $m=2$, and $K_{2,\alpha}=\operatorname{Frac}\bigl(\mathbb C[X,Y]/(P_\alpha)\bigr)$. For a field $L\supseteq\mathbb C$, a *place* of $L$ is a valuation ring $\mathcal O$ of $L$ with $\mathbb C\subseteq\mathcal O\ne L$. A Kähler differential $\omega\in\Omega_{L/\mathbb C}$ is *regular* at $\mathcal O$ if it is a $\mathbb C$-linear combination of differentials $u\,dv$ with $u,v\in\mathcal O$, and *holomorphic* if it is regular at every place. The *genus* $g(L)$ is the dimension over $\mathbb C$ of the space of holomorphic differentials of $L$.
--
--   Then:
--
--   1. $\mathrm{Sym}^+(C_4)$ has exactly four elements;
--   2. $g(K_4)=3$;
--   3. $g(K_{2,\alpha})=2$ for every $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$;
--   4. there are no $a,b,\alpha\in\mathbb C$ with $a\ne0$, $\alpha\ne\bar\alpha$ and $aC_4+b=C_{2,\alpha}$ or $a\overline{C_4}+b=C_{2,\alpha}$.
--
--   In short,
--   $$|\mathrm{Sym}^+(C_4)|=4,\qquad g(K_4)=3,\qquad g(K_{2,\alpha})=2\quad(\alpha\notin\mathbb R),$$
--   and no direct or orientation-reversing similarity carries $C_4$ onto a set $C_{2,\alpha}$ with $\alpha\notin\mathbb R$.
--
--   This is the degree-four example of Remark 5 of the note as printed: $\operatorname{Re}(z^4)=1$ also attains the rotation bound and is not in the $m=2$ family, since its normalization has genus three rather than two. Normalizations are read as function fields, and the family parameter is only required to be nonreal.
--
--   **Formalization Note**: $\mathrm{Sym}^+(S)$ is a subgroup of the isometry group `ℂ ≃ᵢ ℂ`, and its size is `Nat.card` ($0$ for an infinite group). In part 3 the hypothesis $\alpha\ne\bar\alpha$ is a `Fact` instance argument, and the instance $0<2$ needed for $m=2$ is supplied locally.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/PaperRemarks.lean (C. Perassi)

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
attribute [local instance] CurveSymmetry.fact_zero_lt_two

theorem CurveSymmetry.paper_degree_four_genus :
    Nat.card (directIsometryGroup {z : ℂ | (z ^ 4).re = 1}) = 4 ∧
      genus (FermatFunctionField 4) = 3 ∧
      (∀ (α : ℂ) [Fact (α ≠ star α)], genus (FamilyFunctionField 2 α) = 2) ∧
      ¬ ∃ a b α : ℂ, a ≠ 0 ∧ α ≠ star α ∧
        ((fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α ∨
          (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α) := by sorry
