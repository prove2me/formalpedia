-- Prove2me | Theorems.Thm_CurveSymmetry_familyAmbientGroup_algebraic_representative
-- name    : CurveSymmetry.familyAmbientGroup_algebraic_representative
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:48.138091+00:00
-- url     : https://prove2.me/theorems/16bf79a2-3ca2-472f-9804-c0ccd407917e
-- title:
--   For algebraic $\alpha$, every Möbius symmetry of $\widehat{C}_{m,\alpha}$ is induced by a matrix with algebraic entries
-- statement:
--   Let $m\ge 2$ be an integer, let $\alpha\in\mathbb{C}$ satisfy $|\alpha|=1$ and $\alpha\ne\bar\alpha$ (so $\alpha$ is not real), and let $C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$. Let $\widehat{\mathbb{C}}=\mathbb{C}\cup\{\infty\}$ be the Riemann sphere and let $\widehat{C}_{m,\alpha}$ be the closure of $C_{m,\alpha}$ in $\widehat{\mathbb{C}}$. A matrix $h=(h_{jk})\in\mathrm{GL}_2(\mathbb{C})$ acts on $\widehat{\mathbb{C}}$ by the Möbius transformation $p\mapsto(h_{11}p+h_{12})/(h_{21}p+h_{22})$, with the usual conventions at $\infty$ and at the pole. Let $G_{m,\alpha}$ be the group, under composition, of the bijections $\sigma$ of $\widehat{\mathbb{C}}$ that are induced by some matrix in $\mathrm{GL}_2(\mathbb{C})$ and satisfy $\sigma(p)\in\widehat{C}_{m,\alpha}\iff p\in\widehat{C}_{m,\alpha}$ for every $p\in\widehat{\mathbb{C}}$; these are the holomorphic Möbius transformations mapping $\widehat{C}_{m,\alpha}$ onto itself.
--
--   Suppose moreover that $\alpha$ is algebraic over $\mathbb{Q}$, and let $\sigma\in G_{m,\alpha}$. Then $\sigma$ is induced by a matrix with algebraic entries: there is $h=(h_{jk})\in\mathrm{GL}_2(\mathbb{C})$ such that
--
--   $$h_{jk}\in\overline{\mathbb{Q}}\quad(j,k\in\{1,2\})\qquad\text{and}\qquad h\cdot p=\sigma(p)\quad\text{for every } p\in\widehat{\mathbb{C}},$$
--
--   where $\overline{\mathbb{Q}}\subset\mathbb{C}$ is the field of algebraic numbers and $h\cdot p$ is the Möbius action of $h$ described above.
--
--   This is the algebraicity claim of Remark 5 of the note, that for algebraic $\alpha$ all the maps of equation (3) have algebraic coefficients, stated directly for the elements of the group $G_{m,\alpha}$ rather than for the normal forms of (3).
--
--   **Formalization Note**: The sphere is `OnePoint ℂ`. The group $G_{m,\alpha}$ is a subgroup of the permutations of the sphere, namely the image of $\mathrm{GL}_2(\mathbb{C})$ intersected with the stabilizer of $\widehat{C}_{m,\alpha}$, so proportional matrices give the same element; $\widehat{C}_{m,\alpha}$ is the topological closure of the image of $C_{m,\alpha}$. Each of the four entries of $h$ is required to be algebraic over $\mathbb{Q}$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyAlgebraic.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
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
import Mathlib.RingTheory.Algebraic.Integral
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

theorem CurveSymmetry.familyAmbientGroup_algebraic_representative {m : ℕ} (hm : 2 ≤ m)
    {α : ℂ} (ha : α ≠ star α) (hα : ‖α‖ = 1) (halg : IsAlgebraic ℚ α)
    (f : familyAmbientGroup m α) :
    ∃ h : MobiusMatrix, (∀ i j, IsAlgebraic ℚ (h i j)) ∧
      ∀ p : Sphere, h • p = f.val p := by sorry
