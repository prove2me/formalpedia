-- Prove2me | Theorems.Thm_CurveSymmetry_family_anti_mobius_equivalence_iff
-- name    : CurveSymmetry.family_anti_mobius_equivalence_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:59.025094+00:00
-- url     : https://prove2.me/theorems/04125bbc-557f-495b-9efe-cd6cffe1ce9f
-- title:
--   Anti-Möbius equivalence of $\widehat C_{m,\alpha}$ and $\widehat C_{m,\beta}$ holds exactly when $\beta=\bar\alpha$
-- statement:
--   Let $m\ge2$ be an integer and let $\alpha,\beta\in\mathbb C$ with $|\alpha|=|\beta|=1$ and $\alpha,\beta\notin\mathbb R$. For $\gamma\in\{\alpha,\beta\}$ let $C_{m,\gamma}=\{z\in\mathbb C:\operatorname{Re}(z^m(|z|^2+\gamma))=0\}$ and let $\widehat C_{m,\gamma}$ be its closure in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$. A matrix $g=(g_{jk})\in\mathrm{GL}_2(\mathbb C)$ acts on $\widehat{\mathbb C}$ by the Möbius transformation $g\cdot z=\dfrac{g_{11}z+g_{12}}{g_{21}z+g_{22}}$, with the usual conventions at the pole and at $\infty$. Let $\kappa\colon\widehat{\mathbb C}\to\widehat{\mathbb C}$ be complex conjugation, $\kappa(z)=\bar z$, $\kappa(\infty)=\infty$, so that the maps $g\circ\kappa$ are the anti-Möbius maps.
--
--   Then some anti-Möbius map carries $\widehat C_{m,\alpha}$ onto $\widehat C_{m,\beta}$ exactly when the parameters are complex conjugate:
--
--   $$\exists\,g\in\mathrm{GL}_2(\mathbb C):\ (g\circ\kappa)(\widehat C_{m,\alpha})=\widehat C_{m,\beta}\quad\iff\quad\beta=\bar\alpha.$$
--
--   This is the antiholomorphic half of the last assertion of Theorem 2. With its holomorphic counterpart it is used for Remark 5, where the parameters $\alpha=e^{i\theta}$, $0<\theta<\pi$, give pairwise fully Möbius-inequivalent curves.
--
--   **Formalization Note**: the Riemann sphere is the one-point compactification `OnePoint ℂ` and the curves are topological closures in it; matrices act through Mathlib's identification of the sphere with the projective line, and conjugation acts on the sphere fixing $\infty$.
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

theorem CurveSymmetry.family_anti_mobius_equivalence_iff {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) :
    (∃ g : MobiusMatrix,
      (fun p : Sphere => g • OnePoint.map (star : ℂ → ℂ) p) '' sphericalFamily m α =
        sphericalFamily m β) ↔ β = star α := by sorry
