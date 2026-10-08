-- Prove2me | Theorems.Thm_CurveSymmetry_family_mobius_complex_transport
-- name    : CurveSymmetry.family_mobius_complex_transport
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:41:40.574918+00:00
-- url     : https://prove2.me/theorems/11c4a142-54cd-42ee-a796-6c27a50f706f
-- title:
--   A Möbius map sending $\widehat C_{m,\alpha}$ into $\widehat C_{m,\beta}$ carries $V_\alpha$ onto $V_\beta$
-- statement:
--   Let $m\ge1$ be an integer and let $\alpha,\beta\in\mathbb C$ with $\alpha\ne\bar\alpha$ and $\beta\ne\bar\beta$; no condition on their moduli is imposed. For $\gamma\in\{\alpha,\beta\}$ let $\widehat C_{m,\gamma}$ be the closure in the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$ of $C_{m,\gamma}=\{z\in\mathbb C:\operatorname{Re}\bigl(z^m(|z|^2+\gamma)\bigr)=0\}$. For $x=(x_0,x_1)$ and $y=(y_0,y_1)$ in $\mathbb C^2$ let
--
--   $$
--   F_\gamma(x,y)=\gamma\,x_0^m x_1\,y_1^{m+1}+x_0^{m+1}y_0\,y_1^m+\bar\gamma\,x_1^{m+1}y_0^m\,y_1+x_0\,x_1^m\,y_0^{m+1},
--   $$
--
--   the bihomogenization of $P_\gamma(X,Y)=X^m(\gamma+XY)+Y^m(\bar\gamma+XY)$, and let $V_\gamma=\{([x],[y])\in\mathbb P^1\times\mathbb P^1:F_\gamma(x,y)=0\}$.
--
--   Let $g\in\mathrm{GL}_2(\mathbb C)$ with rows $(a,b)$ and $(c,d)$ be any invertible matrix, $M_g(z)=\frac{az+b}{cz+d}$ the Möbius transformation of $\widehat{\mathbb C}$ it defines, and $\bar g$ the matrix with conjugated entries; $\mathrm{GL}_2(\mathbb C)$ acts on $\mathbb P^1$ by $h\,[x]=[hx]$. Assume only the inclusion $M_g(\widehat C_{m,\alpha})\subseteq\widehat C_{m,\beta}$. Then for every $(p_1,p_2)\in\mathbb P^1\times\mathbb P^1$
--
--   $$
--   (g\,p_1,\ \bar g\,p_2)\in V_\beta\iff(p_1,p_2)\in V_\alpha.
--   $$
--
--   In the proof of Theorem 2 a holomorphic Möbius map $M$ acts on the complexification by $(X,Y)\mapsto(M(X),\overline M(Y))$, and the Zariski density of the infinite real locus shows that an equivalence of the spherical real loci carries $V_\alpha$ onto $V_\beta$. This is that step for holomorphic maps, on all of $\mathbb P^1\times\mathbb P^1$, boundary points included.
--
--   **Formalization Note**: Möbius maps are arbitrary matrices in `GL (Fin 2) ℂ` acting on the sphere `OnePoint ℂ` and on $\mathbb P^1$ = `Projectivization ℂ (Fin 2 → ℂ)`; membership in $V_\gamma$ is tested on chosen representatives, which is harmless by bihomogeneity.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), proof of Theorem 2, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyGlobalTransport.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.family_mobius_complex_transport {m : ℕ} (hm : 0 < m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β)
    (p : ProjectiveLine × ProjectiveLine) :
    complexifiedMobius g p ∈ familyProjectiveCurve m β ↔ p ∈ familyProjectiveCurve m α := by sorry
