-- Prove2me | Theorems.Thm_CurveSymmetry_family_mobius_self_mem_iff
-- name    : CurveSymmetry.family_mobius_self_mem_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:26.026104+00:00
-- url     : https://prove2.me/theorems/28d5dc75-23c3-47c4-9d57-7c3705d68797
-- title:
--   A Möbius map carrying $\widehat C_{m,\alpha}$ into itself preserves it exactly
-- statement:
--   Let $m\ge2$ be an integer and let $\alpha\in\mathbb C$ with $|\alpha|=1$ and $\alpha\notin\mathbb R$. Let $C_{m,\alpha}=\{z\in\mathbb C:\operatorname{Re}(z^m(|z|^2+\alpha))=0\}$ and let $\widehat C_{m,\alpha}$ be its closure in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$. A matrix $g=(g_{jk})\in\mathrm{GL}_2(\mathbb C)$ acts on $\widehat{\mathbb C}$ by the Möbius transformation $g\cdot z=\dfrac{g_{11}z+g_{12}}{g_{21}z+g_{22}}$, with the usual conventions at the pole and at $\infty$. Let $g\in\mathrm{GL}_2(\mathbb C)$ satisfy $g(\widehat C_{m,\alpha})\subseteq\widehat C_{m,\alpha}$.
--
--   Then for every $p\in\widehat{\mathbb C}$,
--
--   $$g\cdot p\in\widehat C_{m,\alpha}\iff p\in\widehat C_{m,\alpha}.$$
--
--   Equivalently, the preimage of $\widehat C_{m,\alpha}$ under $g$ is $\widehat C_{m,\alpha}$: the one-sided inclusion is already an exact symmetry.
--
--   This is used for Theorem 2: a Möbius map carrying $\widehat C_{m,\alpha}$ into itself is automatically a symmetry of $\widehat C_{m,\alpha}$, so that, together with the description of the self-inclusions in (3), it identifies the ambient Möbius symmetry group of $\widehat C_{m,\alpha}$.
--
--   **Formalization Note**: the Riemann sphere is the one-point compactification `OnePoint ℂ` and $\widehat C_{m,\alpha}$ is the topological closure of $C_{m,\alpha}$ in it; matrices act through Mathlib's identification of the sphere with the projective line.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Theorem 2, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilySphereClassification.lean (C. Perassi)

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

theorem CurveSymmetry.family_mobius_self_mem_iff {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α) (p : Sphere) :
    g • p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by sorry
