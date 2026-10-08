-- Prove2me | Theorems.Thm_CurveSymmetry_family_arc_equivalence_iff
-- name    : CurveSymmetry.family_arc_equivalence_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:00.818076+00:00
-- url     : https://prove2.me/theorems/a5eeb2ef-9c51-4e90-8b60-539acb3ee3bb
-- title:
--   The parameters $e^{i\theta}$, $0<\theta<\pi$, give pairwise fully Möbius-inequivalent curves $\widehat{C}_{m,\alpha}$
-- statement:
--   Let $m\ge 2$ be an integer. For $\alpha\in\mathbb{C}$ let $C_{m,\alpha}=\{z\in\mathbb{C} : \operatorname{Re}\bigl(z^m(|z|^2+\alpha)\bigr)=0\}$ and let $\widehat{C}_{m,\alpha}$ be its closure in the Riemann sphere $\widehat{\mathbb{C}}=\mathbb{C}\cup\{\infty\}$. A matrix $g=(g_{jk})\in\mathrm{GL}_2(\mathbb{C})$ acts on $\widehat{\mathbb{C}}$ by the Möbius transformation $p\mapsto(g_{11}p+g_{12})/(g_{21}p+g_{22})$, and $\kappa:\widehat{\mathbb{C}}\to\widehat{\mathbb{C}}$ denotes complex conjugation, $\kappa(z)=\bar z$ for $z\in\mathbb{C}$ and $\kappa(\infty)=\infty$. Let $\theta,\varphi\in(0,\pi)$.
--
--   Then $\widehat{C}_{m,e^{i\theta}}$ is carried onto $\widehat{C}_{m,e^{i\varphi}}$ by a Möbius transformation $g$ or by an anti-Möbius transformation $g\circ\kappa$ if and only if $\theta=\varphi$:
--
--   $$\exists\,g\in\mathrm{GL}_2(\mathbb{C}):\ \ g\bigl(\widehat{C}_{m,e^{i\theta}}\bigr)=\widehat{C}_{m,e^{i\varphi}}\ \ \text{or}\ \ g\bigl(\kappa(\widehat{C}_{m,e^{i\theta}})\bigr)=\widehat{C}_{m,e^{i\varphi}}\qquad\Longleftrightarrow\qquad\theta=\varphi.$$
--
--   This is the claim of Remark 5 of the note that, for fixed $m\ge2$, the parameters $\alpha=e^{i\theta}$ with $0<\theta<\pi$ give pairwise fully Möbius-inequivalent curves, a full Möbius equivalence being a holomorphic Möbius map or such a map composed with complex conjugation.
--
--   **Formalization Note**: The sphere is `OnePoint ℂ`, $\widehat{C}_{m,\alpha}$ is the topological closure of the image of $C_{m,\alpha}$, and the equalities are equalities of images of subsets of the sphere.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyParameterArc.lean (C. Perassi)

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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

theorem CurveSymmetry.family_arc_equivalence_iff {m : ℕ} (hm : 2 ≤ m) {θ φ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) (hφ : φ ∈ Set.Ioo 0 Real.pi) :
    ((∃ g : MobiusMatrix, (fun p : Sphere => g • p) ''
        sphericalFamily m (arcParameter θ) = sphericalFamily m (arcParameter φ)) ∨
     (∃ g : MobiusMatrix, (fun p : Sphere => g • OnePoint.map (star : ℂ → ℂ) p) ''
        sphericalFamily m (arcParameter θ) = sphericalFamily m (arcParameter φ))) ↔ θ = φ := by sorry
