-- Prove2me | Theorems.Thm_CurveSymmetry_mobius_antidiagonal_action
-- name    : CurveSymmetry.mobius_antidiagonal_action
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:43:47.308459+00:00
-- url     : https://prove2.me/theorems/74b7ac77-4375-4055-9a9e-6647cd7a5370
-- title:
--   A Möbius map with antidiagonal matrix acts on the whole sphere as $z\mapsto\lambda/z$ with $\lambda\ne0$
-- statement:
--   Let $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$ be the Riemann sphere. A matrix $g\in\mathrm{GL}_2(\mathbb C)$ with rows $(a,b)$ and $(c,d)$ acts on $\widehat{\mathbb C}$ by the Möbius transformation $M_g(z)=\dfrac{az+b}{cz+d}$, with the usual conventions: if $c\ne0$ then $M_g(-d/c)=\infty$ and $M_g(\infty)=a/c$, and if $c=0$ then $M_g(\infty)=\infty$. For $\gamma\in\mathbb C$ let $s_\gamma:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be the map with $s_\gamma(0)=\infty$, $s_\gamma(\infty)=0$ and $s_\gamma(z)=\gamma/z$ for $z\in\mathbb C\setminus\{0\}$.
--
--   Suppose that $a=0$ and $d=0$. Then:
--
--   1. $b/c\ne0$;
--   2. $M_g$ agrees with $s_{b/c}$ at every point of the sphere:
--
--      $$
--      M_g(p)=s_{b/c}(p)\qquad\text{for all }p\in\widehat{\mathbb C}.
--      $$
--
--   Theorem 2 of the note lists the ambient symmetries of $\widehat C_{m,\alpha}$ as maps $z\mapsto\lambda z$ and $z\mapsto\lambda/z$ with constant $\lambda$, equation (3). This lemma identifies the Möbius maps with antidiagonal matrices with maps of the second kind, including their values at $0$ and $\infty$; the formalization uses it to bring Möbius maps that exchange $0$ and $\infty$ into this form.
--
--   **Formalization Note**: $\widehat{\mathbb C}$ is `OnePoint ℂ` and $M_g$ is Mathlib's action of `GL (Fin 2) ℂ` on it; $a,b,c,d$ are the entries `g 0 0`, `g 0 1`, `g 1 0`, `g 1 1`.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, used for Theorem 1 (p. 1), Theorem 2 (p. 2), Lemma 4 (p. 3), https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/MobiusPair.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
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
open OnePoint

theorem CurveSymmetry.mobius_antidiagonal_action (g : MobiusMatrix) (ha : g 0 0 = 0) (hd : g 1 1 = 0) :
    g 0 1 / g 1 0 ≠ 0 ∧ ∀ p : Sphere, g • p = sphereInversion (g 0 1 / g 1 0) p := by sorry
