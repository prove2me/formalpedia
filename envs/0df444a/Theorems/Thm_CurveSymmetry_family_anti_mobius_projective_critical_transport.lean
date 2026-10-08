-- Prove2me | Theorems.Thm_CurveSymmetry_family_anti_mobius_projective_critical_transport
-- name    : CurveSymmetry.family_anti_mobius_projective_critical_transport
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:53.01825+00:00
-- url     : https://prove2.me/theorems/be1100d5-2f34-453a-8d24-14242573ac09
-- title:
--   Anti-Möbius transport of the singular points of $V_\alpha$ onto those of $V_\beta$
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha,\beta\in\mathbb C$ with $\alpha\ne\bar\alpha$ and $\beta\ne\bar\beta$; no condition on their moduli is imposed. For $\gamma\in\{\alpha,\beta\}$ let $\widehat C_{m,\gamma}$ be the closure in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$ of $C_{m,\gamma}=\{z\in\mathbb C:\operatorname{Re}\bigl(z^m(|z|^2+\gamma)\bigr)=0\}$, and for $x=(x_0,x_1)$, $y=(y_0,y_1)$ in $\mathbb C^2$ let
--
--   $$
--   F_\gamma(x,y)=\gamma\,x_0^m x_1\,y_1^{m+1}+x_0^{m+1}y_0\,y_1^m+\bar\gamma\,x_1^{m+1}y_0^m\,y_1+x_0\,x_1^m\,y_0^{m+1},
--   $$
--
--   the bihomogenization of $P_\gamma(X,Y)=X^m(\gamma+XY)+Y^m(\bar\gamma+XY)$. Let $\Sigma_\gamma\subset\mathbb P^1\times\mathbb P^1$ be the set of points $([x],[y])$ at which $F_\gamma$, as a function on $\mathbb C^2\times\mathbb C^2$, vanishes together with its differential: the singular points of the curve $V_\gamma=\{F_\gamma=0\}$ by the Jacobian criterion, independently of the representatives.
--
--   Let $g\in\mathrm{GL}_2(\mathbb C)$ with rows $(a,b)$ and $(c,d)$ be any invertible matrix, $M_g(z)=\frac{az+b}{cz+d}$ the Möbius transformation of $\widehat{\mathbb C}$ it defines, and $\bar g$ the matrix with conjugated entries; $\mathrm{GL}_2(\mathbb C)$ acts on $\mathbb P^1$ by $h\,[x]=[hx]$, and $p\mapsto\bar p$ is complex conjugation on $\widehat{\mathbb C}$, with $\bar\infty=\infty$. Assume that $M_g(\bar p)\in\widehat C_{m,\beta}$ for every $p\in\widehat C_{m,\alpha}$. Then for every $(p_1,p_2)\in\mathbb P^1\times\mathbb P^1$
--
--   $$
--   (g\,p_2,\ \bar g\,p_1)\in\Sigma_\beta\iff(p_1,p_2)\in\Sigma_\alpha.
--   $$
--
--   In the proof of Theorem 2 an equivalence of the spherical real loci must preserve the singular points of $V_\alpha$ and $V_\beta$. This is that statement for anti-Möbius maps: the map $(p_1,p_2)\mapsto(g\,p_2,\bar g\,p_1)$ of $\mathbb P^1\times\mathbb P^1$ induced by $p\mapsto M_g(\bar p)$ matches the two singular loci. Only the inclusion of the spherical curves is assumed, with no condition on the form of $g$.
--
--   **Formalization Note**: the conjugation of the sphere `OnePoint ℂ` is `OnePoint.map star`, and the singular locus is defined through `HasFDerivAt` at chosen representatives in `Projectivization ℂ (Fin 2 → ℂ)`.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 2, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/HomogeneousDifferential.lean (C. Perassi)

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

theorem CurveSymmetry.family_anti_mobius_projective_critical_transport {m : ℕ} (hm : 0 < m)
    {α β : ℂ} (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α,
      g • OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m β)
    (p : ProjectiveLine × ProjectiveLine) :
    complexifiedAntiMobius g p ∈ familyProjectiveCritical m β ↔
      p ∈ familyProjectiveCritical m α := by sorry
