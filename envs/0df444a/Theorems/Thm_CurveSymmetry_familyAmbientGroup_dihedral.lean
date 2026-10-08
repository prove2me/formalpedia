-- Prove2me | Theorems.Thm_CurveSymmetry_familyAmbientGroup_dihedral
-- name    : CurveSymmetry.familyAmbientGroup_dihedral
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:54.068237+00:00
-- url     : https://prove2.me/theorems/b1af035b-fe5e-42af-b48b-2b9e5b38a718
-- title:
--   The Möbius symmetry group of $\widehat{C}_{m,\alpha}$ is dihedral of order $4m$
-- statement:
--   Let $m\ge 2$ be an integer, let $\alpha\in\mathbb{C}$ satisfy $|\alpha|=1$ and $\alpha\ne\bar\alpha$ (so $\alpha$ is not real), and let $C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$. Let $\widehat{\mathbb{C}}=\mathbb{C}\cup\{\infty\}$ be the Riemann sphere and let $\widehat{C}_{m,\alpha}$ be the closure of $C_{m,\alpha}$ in $\widehat{\mathbb{C}}$. A matrix $h=(h_{jk})\in\mathrm{GL}_2(\mathbb{C})$ acts on $\widehat{\mathbb{C}}$ by the Möbius transformation $p\mapsto(h_{11}p+h_{12})/(h_{21}p+h_{22})$, with the usual conventions at $\infty$ and at the pole. Let $G_{m,\alpha}$ be the group, under composition, of the bijections $\sigma$ of $\widehat{\mathbb{C}}$ that are induced by some matrix in $\mathrm{GL}_2(\mathbb{C})$ and satisfy $\sigma(p)\in\widehat{C}_{m,\alpha}\iff p\in\widehat{C}_{m,\alpha}$ for every $p\in\widehat{\mathbb{C}}$; these are the holomorphic Möbius transformations mapping $\widehat{C}_{m,\alpha}$ onto itself.
--
--   Then $G_{m,\alpha}$ is isomorphic to the dihedral group of order $4m$, the symmetry group of a regular $2m$-gon:
--
--   $$G_{m,\alpha}\;\cong\;\langle\, r,s \mid r^{2m}=s^{2}=1,\ srs=r^{-1}\,\rangle .$$
--
--   Theorem 2 of the note states that the full ambient symmetry group of $\widehat{C}_{m,\alpha}$, anti-Möbius maps included, consists of the maps of equation (3) and is dihedral of order $4m$. The group here contains only holomorphic Möbius maps; that no anti-Möbius map (a Möbius map composed with complex conjugation) preserves $\widehat{C}_{m,\alpha}$ is a separate result, so $G_{m,\alpha}$ is the full group of Theorem 2. The quartic case $m=2$ is included.
--
--   **Formalization Note**: The sphere is `OnePoint ℂ`. The group $G_{m,\alpha}$ is a subgroup of the permutations of the sphere, namely the image of $\mathrm{GL}_2(\mathbb{C})$ intersected with the stabilizer of $\widehat{C}_{m,\alpha}$, so proportional matrices give the same element; $\widehat{C}_{m,\alpha}$ is the topological closure of the image of $C_{m,\alpha}$. The dihedral group is Mathlib's `DihedralGroup (2 * m)`, which has $4m$ elements.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Theorem 2 and equation (3), p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyDihedral.lean (C. Perassi)

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
import Mathlib.GroupTheory.SpecificGroups.Dihedral
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
open OnePoint

theorem CurveSymmetry.familyAmbientGroup_dihedral {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    Nonempty (DihedralGroup (2 * m) ≃* familyAmbientGroup m α) := by sorry
