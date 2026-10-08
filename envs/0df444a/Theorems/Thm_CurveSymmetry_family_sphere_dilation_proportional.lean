-- Prove2me | Theorems.Thm_CurveSymmetry_family_sphere_dilation_proportional
-- name    : CurveSymmetry.family_sphere_dilation_proportional
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:42:00.23235+00:00
-- url     : https://prove2.me/theorems/b1aab910-ae96-46c4-9153-cfe6bf1bde74
-- title:
--   A dilation $z\mapsto cz$ mapping $\widehat C_{m,\alpha}$ into $\widehat C_{m,\beta}$ yields proportional equations
-- statement:
--   Let $m\ge1$ be an integer, let $\alpha,\beta\in\mathbb C\setminus\mathbb R$ (no condition on their moduli), and let $c\in\mathbb C$ with $c\ne0$. For $\gamma\in\mathbb C$ put $P_\gamma(X,Y)=X^m(\gamma+XY)+Y^m(\bar\gamma+XY)$, as in equation (6), and $C_{m,\gamma}=\{z\in\mathbb C:\operatorname{Re}(z^m(|z|^2+\gamma))=0\}$, so that $P_\gamma(z,\bar z)=2\operatorname{Re}(z^m(|z|^2+\gamma))$. Let $\widehat C_{m,\gamma}$ be the closure of $C_{m,\gamma}$ in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$, and let $D_c\colon\widehat{\mathbb C}\to\widehat{\mathbb C}$ be the dilation $D_c(z)=cz$ for $z\in\mathbb C$, $D_c(\infty)=\infty$.
--
--   Assume that $D_c(\widehat C_{m,\alpha})\subseteq\widehat C_{m,\beta}$. Then there is $k\in\mathbb C$ with $k\ne0$ such that, as polynomials in $\mathbb C[X,Y]$,
--
--   $$P_\beta(cX,\bar cY)=k\,P_\alpha(X,Y).$$
--
--   The left side is the pullback of $P_\beta$ by $z\mapsto cz$, with $X$ and $Y$ standing for $z$ and $\bar z$.
--
--   In Theorem 2 an ambient equivalence between the curves is reduced to the forms $cz$, $c/z$, $c\bar z$, $c/\bar z$. This result turns the dilation case into a proportionality of polynomials, from which the ratio in (8) and the condition $c^{2m}=1$ in (3) are obtained; the hypothesis is only an inclusion of the spherical closures. Through Theorem 2 it is also used for Theorem 1 and Remark 5.
--
--   **Formalization Note**: the Riemann sphere is the one-point compactification `OnePoint ℂ`, $\widehat C_{m,\gamma}$ is the topological closure in it, and $D_c$ is defined pointwise on the sphere.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Theorem 2, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilySphereDilation.lean (C. Perassi)

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
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial OnePoint

theorem CurveSymmetry.family_sphere_dilation_proportional {m : ℕ} (hm : 0 < m) {α β c : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hc : c ≠ 0)
    (hmap : ∀ p ∈ sphericalFamily m α, sphereDilation c p ∈ sphericalFamily m β) :
    ∃ k : ℂ, k ≠ 0 ∧ dilate c (familyPolynomial m β) = C k * familyPolynomial m α := by sorry
