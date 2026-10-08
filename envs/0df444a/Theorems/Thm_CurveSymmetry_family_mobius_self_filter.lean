-- Prove2me | Theorems.Thm_CurveSymmetry_family_mobius_self_filter
-- name    : CurveSymmetry.family_mobius_self_filter
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:57.910772+00:00
-- url     : https://prove2.me/theorems/227bfd13-21f3-4b35-b2a3-88eb0bd6f588
-- title:
--   The Möbius maps sending $\widehat C_{m,\alpha}$ into itself are $cz$, $c^{2m}=1$, and $c/z$, $c^{2m}=\bar\alpha^2$
-- statement:
--   Let $m\ge2$ be an integer and let $\alpha\in\mathbb C$ with $|\alpha|=1$ and $\alpha\notin\mathbb R$. Let $C_{m,\alpha}=\{z\in\mathbb C:\operatorname{Re}(z^m(|z|^2+\alpha))=0\}$ and let $\widehat C_{m,\alpha}$ be its closure in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$. A matrix $g=(g_{jk})\in\mathrm{GL}_2(\mathbb C)$ acts on $\widehat{\mathbb C}$ by the Möbius transformation $g\cdot z=\dfrac{g_{11}z+g_{12}}{g_{21}z+g_{22}}$, with the usual conventions at the pole and at $\infty$. For $c\ne0$ let $D_c$ and $J_c$ be the maps of $\widehat{\mathbb C}$ given by $D_c(z)=cz$, $D_c(\infty)=\infty$, and $J_c(z)=c/z$ for $z\ne0$, $J_c(0)=\infty$, $J_c(\infty)=0$.
--
--   Then for every $g\in\mathrm{GL}_2(\mathbb C)$,
--
--   $$g(\widehat C_{m,\alpha})\subseteq\widehat C_{m,\alpha}\iff\exists\,c\in\mathbb C\setminus\{0\}:\ \bigl(c^{2m}=1\ \text{and}\ g=D_c\bigr)\ \text{or}\ \bigl(c^{2m}=\bar\alpha^{2}\ \text{and}\ g=J_c\bigr),$$
--
--   where $g=D_c$ means $g\cdot p=D_c(p)$ for every $p\in\widehat{\mathbb C}$, and likewise for $J_c$.
--
--   This is the description (3) of the ambient Möbius symmetries of $\widehat C_{m,\alpha}$ in Theorem 2, for an arbitrary invertible matrix, on all points of the sphere, and with a one-sided inclusion as hypothesis. It is also used for Remark 5 and, in the formalization, for the classification of the affine self-maps of $C_{m,\alpha}$.
--
--   **Formalization Note**: the Riemann sphere is the one-point compactification `OnePoint ℂ` and $\widehat C_{m,\alpha}$ is the topological closure of $C_{m,\alpha}$ in it; matrices act through Mathlib's identification of the sphere with the projective line.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Theorem 2, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilySphereClassification.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
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
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

open CurveSymmetry
set_option autoImplicit false

theorem CurveSymmetry.family_mobius_self_filter {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (g : MobiusMatrix) :
    (∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α) ↔
      ∃ c : ℂ, c ≠ 0 ∧
        ((c ^ (2 * m) = 1 ∧ ∀ p : Sphere, g • p = sphereDilation c p) ∨
         (c ^ (2 * m) = star α ^ 2 ∧ ∀ p : Sphere, g • p = sphereInversion c p)) := by sorry
