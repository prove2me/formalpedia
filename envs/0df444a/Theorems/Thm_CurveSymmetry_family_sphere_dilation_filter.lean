-- Prove2me | Theorems.Thm_CurveSymmetry_family_sphere_dilation_filter
-- name    : CurveSymmetry.family_sphere_dilation_filter
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:58.279823+00:00
-- url     : https://prove2.me/theorems/679549df-56bd-4102-9a5b-8ad1af069a75
-- title:
--   For $|\alpha|=1$, the map $z\mapsto cz$ sends $\widehat C_{m,\alpha}$ into itself if and only if $c^{2m}=1$
-- statement:
--   Let $m\ge1$ be an integer, let $\alpha\in\mathbb C$ with $|\alpha|=1$ and $\alpha\notin\mathbb R$, and let $c\in\mathbb C$ with $c\ne0$. Let $C_{m,\alpha}=\{z\in\mathbb C:\operatorname{Re}(z^m(|z|^2+\alpha))=0\}$, let $\widehat C_{m,\alpha}$ be its closure in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$, and let $D_c\colon\widehat{\mathbb C}\to\widehat{\mathbb C}$ be the dilation $D_c(z)=cz$ for $z\in\mathbb C$, $D_c(\infty)=\infty$. Then
--
--   $$D_c(\widehat C_{m,\alpha})\subseteq\widehat C_{m,\alpha}\iff c^{2m}=1.$$
--
--   This is the dilation half of the description (3) of the ambient Möbius symmetries of $\widehat C_{m,\alpha}$ in Theorem 2, tested on the whole sphere, $\infty$ included. It is also used for Remark 5.
--
--   **Formalization Note**: the Riemann sphere is the one-point compactification `OnePoint ℂ`, $\widehat C_{m,\alpha}$ is the topological closure in it, and $D_c$ is defined pointwise on the sphere.
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

theorem CurveSymmetry.family_sphere_dilation_filter {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hc : c ≠ 0) :
    (∀ p ∈ sphericalFamily m α, sphereDilation c p ∈ sphericalFamily m α) ↔
      c ^ (2 * m) = 1 := by sorry
