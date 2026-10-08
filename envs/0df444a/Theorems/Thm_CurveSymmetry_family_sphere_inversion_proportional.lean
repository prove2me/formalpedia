-- Prove2me | Theorems.Thm_CurveSymmetry_family_sphere_inversion_proportional
-- name    : CurveSymmetry.family_sphere_inversion_proportional
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:17.649208+00:00
-- url     : https://prove2.me/theorems/67ef687f-16e1-4a2e-8ff6-ca998dc7e4cd
-- title:
--   An inversion $z\mapsto c/z$ mapping $\widehat C_{m,\alpha}$ into $\widehat C_{m,\beta}$ yields proportional equations
-- statement:
--   Let $m\ge1$ be an integer, let $\alpha,\beta\in\mathbb C\setminus\mathbb R$ (no condition on their moduli), and let $c\in\mathbb C$ with $c\ne0$. For $\gamma\in\mathbb C$ put $P_\gamma(X,Y)=X^m(\gamma+XY)+Y^m(\bar\gamma+XY)$, as in equation (6), and $C_{m,\gamma}=\{z\in\mathbb C:\operatorname{Re}(z^m(|z|^2+\gamma))=0\}$, so that $P_\gamma(z,\bar z)=2\operatorname{Re}(z^m(|z|^2+\gamma))$. Let $\widehat C_{m,\gamma}$ be the closure of $C_{m,\gamma}$ in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$, and let $J_c\colon\widehat{\mathbb C}\to\widehat{\mathbb C}$ be the inversion $J_c(z)=c/z$ for $z\in\mathbb C\setminus\{0\}$, $J_c(0)=\infty$, $J_c(\infty)=0$.
--
--   Assume that $J_c(\widehat C_{m,\alpha})\subseteq\widehat C_{m,\beta}$. Then there is $k\in\mathbb C$ with $k\ne0$ such that, as polynomials in $\mathbb C[X,Y]$,
--
--   $$|c|^2\,\bar c^{\,m}X^m+|c|^2\,c^mY^m+XY\bigl(\bar c^{\,m}\bar\beta\,X^m+c^m\beta\,Y^m\bigr)=k\,P_\alpha(X,Y).$$
--
--   The left side equals $X^{m+1}Y^{m+1}P_\beta(c/X,\bar c/Y)$: it is the pullback of $P_\beta$ by $z\mapsto c/z$ (with $X$, $Y$ standing for $z$, $\bar z$), with the denominator cleared.
--
--   In Theorem 2 an ambient equivalence between the curves is reduced to the forms $cz$, $c/z$, $c\bar z$, $c/\bar z$. This result treats the inversion case: the cleared pullback of $P_\beta$ is proportional to $P_\alpha$, which yields the ratio in (8) and the condition $c^{2m}=\bar\alpha^{2}$ in (3). The hypothesis is an inclusion on the whole sphere, including the point $0$, which $J_c$ sends to $\infty$. Through Theorem 2 it is also used for Theorem 1 and Remark 5.
--
--   **Formalization Note**: the Riemann sphere is the one-point compactification `OnePoint ℂ`, $\widehat C_{m,\gamma}$ is the topological closure in it, and $J_c$ is defined pointwise on the sphere with the values above at $0$ and $\infty$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Theorem 2, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilySphereInversion.lean (C. Perassi)

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

theorem CurveSymmetry.family_sphere_inversion_proportional {m : ℕ} (hm : 0 < m) {α β c : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hc : c ≠ 0)
    (hmap : ∀ p ∈ sphericalFamily m α, sphereInversion c p ∈ sphericalFamily m β) :
    ∃ k : ℂ, k ≠ 0 ∧ inversionFamily m β c = C k * familyPolynomial m α := by sorry
