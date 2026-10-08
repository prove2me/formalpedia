-- Prove2me | Theorems.Thm_CurveSymmetry_familyAmbientGroup_card
-- name    : CurveSymmetry.familyAmbientGroup_card
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:02.501392+00:00
-- url     : https://prove2.me/theorems/6dd65b14-a4f1-4ad9-9e94-8450871a1fef
-- title:
--   The Möbius symmetry group of $\widehat{C}_{m,\alpha}$ has exactly $4m$ elements
-- statement:
--   Let $m\ge 2$ be an integer, let $\alpha\in\mathbb{C}$ satisfy $|\alpha|=1$ and $\alpha\ne\bar\alpha$ (so $\alpha$ is not real), and let $C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$. Let $\widehat{\mathbb{C}}=\mathbb{C}\cup\{\infty\}$ be the Riemann sphere and let $\widehat{C}_{m,\alpha}$ be the closure of $C_{m,\alpha}$ in $\widehat{\mathbb{C}}$. A matrix $h=(h_{jk})\in\mathrm{GL}_2(\mathbb{C})$ acts on $\widehat{\mathbb{C}}$ by the Möbius transformation $p\mapsto(h_{11}p+h_{12})/(h_{21}p+h_{22})$, with the usual conventions at $\infty$ and at the pole. Let $G_{m,\alpha}$ be the group, under composition, of the bijections $\sigma$ of $\widehat{\mathbb{C}}$ that are induced by some matrix in $\mathrm{GL}_2(\mathbb{C})$ and satisfy $\sigma(p)\in\widehat{C}_{m,\alpha}\iff p\in\widehat{C}_{m,\alpha}$ for every $p\in\widehat{\mathbb{C}}$; these are the holomorphic Möbius transformations mapping $\widehat{C}_{m,\alpha}$ onto itself.
--
--   Then $G_{m,\alpha}$ is finite, with
--
--   $$|G_{m,\alpha}|=4m.$$
--
--   This is the order of the ambient symmetry group in Theorem 2 of the note, whose elements are the maps of equation (3): $z\mapsto cz$ with $c^{2m}=1$, and $z\mapsto c/z$ with $c^{2m}=\bar\alpha^{2}$. Anti-Möbius maps are not elements of $G_{m,\alpha}$; that none of them preserves $\widehat{C}_{m,\alpha}$ is a separate result. The quartic case $m=2$ is included.
--
--   **Formalization Note**: The sphere is `OnePoint ℂ`. The group $G_{m,\alpha}$ is a subgroup of the permutations of the sphere, namely the image of $\mathrm{GL}_2(\mathbb{C})$ intersected with the stabilizer of $\widehat{C}_{m,\alpha}$, so proportional matrices give the same element; $\widehat{C}_{m,\alpha}$ is the topological closure of the image of $C_{m,\alpha}$. The cardinality is `Nat.card`, so the equation also asserts finiteness.
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

theorem CurveSymmetry.familyAmbientGroup_card {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    Nat.card (familyAmbientGroup m α) = 4 * m := by sorry
