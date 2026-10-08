-- Prove2me | Theorems.Thm_CurveSymmetry_family_bihomogeneous_transport
-- name    : CurveSymmetry.family_bihomogeneous_transport
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:47.951742+00:00
-- url     : https://prove2.me/theorems/cbce8f90-a2b3-4ef0-9fb1-841679e8c3de
-- title:
--   A scalar identity for the cleared Möbius pullback of $P_\beta$ extends to all homogeneous coordinates
-- statement:
--   Let $m\ge0$ be an integer and let $\alpha,\beta,k\in\mathbb C$ be arbitrary. For $\gamma\in\mathbb C$ put $P_\gamma(X,Y)=X^m(\gamma+XY)+Y^m(\bar\gamma+XY)$ and let $F_\gamma$ be its bihomogenization of bidegree $(m+1,m+1)$, so that $F_\gamma\bigl((X,1),(Y,1)\bigr)=P_\gamma(X,Y)$: for $x=(x_0,x_1)$ and $y=(y_0,y_1)$ in $\mathbb C^2$,
--
--   $$
--   F_\gamma(x,y)=\gamma\,x_0^m x_1\,y_1^{m+1}+x_0^{m+1}y_0\,y_1^m+\bar\gamma\,x_1^{m+1}y_0^m\,y_1+x_0\,x_1^m\,y_0^{m+1}.
--   $$
--
--   Let $g\in\mathrm{GL}_2(\mathbb C)$ act on column vectors of $\mathbb C^2$, and let $\bar g$ be the matrix with complex-conjugated entries. The cleared pullback of $P_\beta$ by $g$ is the polynomial $P_\beta^{g}(X,Y)=F_\beta\bigl(g\,(X,1)^{\mathsf T},\ \bar g\,(Y,1)^{\mathsf T}\bigr)\in\mathbb C[X,Y]$. For $g$ with rows $(a,b)$ and $(c,d)$ it equals, as a rational function, $(cX+d)^{m+1}(\bar cY+\bar d)^{m+1}P_\beta\bigl(M(X),\overline M(Y)\bigr)$, where $M(X)=\frac{aX+b}{cX+d}$ and $\overline M(Y)=\frac{\bar aY+\bar b}{\bar cY+\bar d}$.
--
--   Assume the polynomial identity $P_\beta^{g}=k\,P_\alpha$ in $\mathbb C[X,Y]$. Then for all $x,y\in\mathbb C^2$
--
--   $$
--   F_\beta(gx,\ \bar g\,y)=k\,F_\alpha(x,y).
--   $$
--
--   In the proof of Theorem 2 the note substitutes a Möbius map into $P_\beta$, clears denominators and compares the result with $P_\alpha$. This lemma extends such an identity from the affine chart to all homogeneous coordinates, including the points with $x_1=0$ or $y_1=0$ that lie over the boundary of $\mathbb P^1\times\mathbb P^1$. It is the algebraic step behind the claim that an equivalence of the spherical real loci carries $V_\alpha$ onto $V_\beta$.
--
--   **Formalization Note**: $\bar g$ is the entrywise conjugate of $g$ in `GL (Fin 2) ℂ`, $g$ acts on `Fin 2 → ℂ` by matrix–vector multiplication, and the hypothesis is an equality in `MvPolynomial (Fin 2) ℂ`.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for proof of Theorem 2, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FamilyGlobalTransport.lean (C. Perassi)

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

theorem CurveSymmetry.family_bihomogeneous_transport {m : ℕ} {α β k : ℂ} {g : MobiusMatrix}
    (he : familyMobiusPullback m β g = C k * familyPolynomial m α)
    (x y : Fin 2 → ℂ) :
    familyBihomogeneous m β (g • x) ((g.map (starRingEnd ℂ)) • y) =
      k * familyBihomogeneous m α x y := by sorry
