-- Prove2me | Theorems.Thm_CurveSymmetry_criticalZero_transport
-- name    : CurveSymmetry.criticalZero_transport
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:28.272728+00:00
-- url     : https://prove2.me/theorems/99b43b54-a64d-44f4-8e55-4453c7eb7047
-- title:
--   Critical zeros are preserved by linear automorphisms and by nonzero scalar factors
-- statement:
--   Let $\mathbb K$ be a nontrivially normed field (for example $\mathbb R$ or $\mathbb C$) and let $E$ be a normed vector space over $\mathbb K$. For a function $H:E\to\mathbb K$, call $x\in E$ a *critical zero* of $H$ if $H(x)=0$ and $H$ is Fréchet differentiable at $x$ with derivative $0$.
--
--   Let $T:E\to E$ be a $\mathbb K$-linear bijection which is continuous with continuous inverse, let $F,G:E\to\mathbb K$ be arbitrary functions, and let $k\in\mathbb K$, $k\ne0$, satisfy $G(Tx)=k\,F(x)$ for all $x\in E$. Then for every $x\in E$
--
--   $$
--   Tx\ \text{is a critical zero of}\ G\iff x\ \text{is a critical zero of}\ F.
--   $$
--
--   This is the invariance principle for the homogeneous Jacobian condition that defines the singular points of the curve $V_\alpha\subset\mathbb P^1\times\mathbb P^1$ of Lemma 4. The formalization applies it to the linear maps induced by Möbius matrices, to rescalings of homogeneous coordinates, to changes of chart and to the exchange of the two factors of $\mathbb P^1\times\mathbb P^1$. No regularity of $F$ or $G$ is assumed.
--
--   **Formalization Note**: the condition is `H x = 0 ∧ HasFDerivAt H 0 x`. Using `HasFDerivAt` rather than the totalized derivative `fderiv` means that a point where $H$ is not differentiable is never a critical zero. $T$ is a continuous linear equivalence `E ≃L[𝕜] E`.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Theorem 2 (p. 2), Lemma 4 (p. 3), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/HomogeneousDifferential.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
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

theorem CurveSymmetry.criticalZero_transport {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : E ≃L[𝕜] E) {F G : E → 𝕜} {k : 𝕜} (hk : k ≠ 0)
    (he : ∀ x, G (T x) = k * F x) (x : E) :
    CriticalZero G (T x) ↔ CriticalZero F x := by sorry
