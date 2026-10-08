-- Prove2me | Theorems.Thm_CurveSymmetry_familyAmbientGroup_generators
-- name    : CurveSymmetry.familyAmbientGroup_generators
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:22.041985+00:00
-- url     : https://prove2.me/theorems/4fbaa08e-e81c-49f7-8780-2afcbba8dcc9
-- title:
--   Generators $r,s$ of the Möbius symmetry group of $\widehat{C}_{m,\alpha}$ with $r^{2m}=s^2=1$ and $srs=r^{-1}$
-- statement:
--   Let $m\ge 2$ be an integer, let $\alpha\in\mathbb{C}$ satisfy $|\alpha|=1$ and $\alpha\ne\bar\alpha$ (so $\alpha$ is not real), and let $C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$. Let $\widehat{\mathbb{C}}=\mathbb{C}\cup\{\infty\}$ be the Riemann sphere and let $\widehat{C}_{m,\alpha}$ be the closure of $C_{m,\alpha}$ in $\widehat{\mathbb{C}}$. A matrix $h=(h_{jk})\in\mathrm{GL}_2(\mathbb{C})$ acts on $\widehat{\mathbb{C}}$ by the Möbius transformation $p\mapsto(h_{11}p+h_{12})/(h_{21}p+h_{22})$, with the usual conventions at $\infty$ and at the pole. Let $G_{m,\alpha}$ be the group, under composition, of the bijections $\sigma$ of $\widehat{\mathbb{C}}$ that are induced by some matrix in $\mathrm{GL}_2(\mathbb{C})$ and satisfy $\sigma(p)\in\widehat{C}_{m,\alpha}\iff p\in\widehat{C}_{m,\alpha}$ for every $p\in\widehat{\mathbb{C}}$; these are the holomorphic Möbius transformations mapping $\widehat{C}_{m,\alpha}$ onto itself.
--
--   Then there exist $r,s\in G_{m,\alpha}$ such that:
--
--   1. $r$ has order exactly $2m$;
--   2. $s$ has order exactly $2$;
--   3. $srs=r^{-1}$, where products are compositions of maps of $\widehat{\mathbb{C}}$;
--   4. every $g\in G_{m,\alpha}$ equals $r^i$ or $sr^i$ for some integer $i$ with $0\le i<2m$.
--
--   In other words,
--
--   $$G_{m,\alpha}=\{\,r^i,\ sr^i : 0\le i<2m\,\},\qquad \operatorname{ord}(r)=2m,\quad \operatorname{ord}(s)=2,\quad srs=r^{-1}.$$
--
--   These are the dihedral generators and relations of Theorem 2 of the note, where the generators are the rotation $z\mapsto e^{\pi i/m}z$ and an inversion $z\mapsto c_0/z$ with $c_0^m=\bar\alpha$; the statement here asserts only that such generators exist. The quartic case $m=2$ is included.
--
--   **Formalization Note**: The sphere is `OnePoint ℂ`. The group $G_{m,\alpha}$ is a subgroup of the permutations of the sphere, namely the image of $\mathrm{GL}_2(\mathbb{C})$ intersected with the stabilizer of $\widehat{C}_{m,\alpha}$, so proportional matrices give the same element; $\widehat{C}_{m,\alpha}$ is the topological closure of the image of $C_{m,\alpha}$.
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

theorem CurveSymmetry.familyAmbientGroup_generators {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    ∃ r s : familyAmbientGroup m α,
      orderOf r = 2 * m ∧ orderOf s = 2 ∧ s * r * s = r⁻¹ ∧
      ∀ g, ∃ i : ℕ, i < 2 * m ∧ (g = r ^ i ∨ g = s * r ^ i) := by sorry
