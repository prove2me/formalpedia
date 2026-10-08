-- Prove2me | Theorems.Thm_CurveSymmetry_paper_isometry_sign
-- name    : CurveSymmetry.paper_isometry_sign
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:10.933321+00:00
-- url     : https://prove2.me/theorems/280ce515-61ef-4214-a546-228db78faa42
-- title:
--   Lemma 3 (sign clause): $f\circ T=\pm f$ for every $T\in\mathrm{Sym}(C)$, and $f\circ T=f$ if $T$ reverses orientation
-- statement:
--   Let $f\in\mathbb{R}[x,y]$ be irreducible in $\mathbb{C}[x,y]$ and of total degree at least $2$. Identify $\mathbb{R}^2$ with $\mathbb{C}$ and write $f(z)=f(\operatorname{Re}z,\operatorname{Im}z)$ for $z\in\mathbb{C}$. Let $C=\{z\in\mathbb{C} : f(z)=0\}$ be the real zero set, assumed infinite, and let $\mathrm{Sym}(C)$ be the group of isometries $T$ of the Euclidean plane with $T(z)\in C\iff z\in C$ for every $z\in\mathbb{C}$. Let $T\in\mathrm{Sym}(C)$.
--
--   Then there is a real number $\varepsilon\in\{1,-1\}$ such that
--
--   $$f\bigl(T(z)\bigr)=\varepsilon\,f(z)\qquad\text{for every } z\in\mathbb{C},$$
--
--   and $\varepsilon=1$ whenever $T$ reverses orientation, that is, whenever there are $a,b\in\mathbb{C}$ with $T(z)=a\bar z+b$ for all $z$.
--
--   This is the sign clause of Lemma 3 of the note: $f\circ T=\varepsilon(T)f$ with $\varepsilon(T)\in\{1,-1\}$, and $\varepsilon(T)=1$ if $T$ is a reflection. Here the last condition is stated for every orientation-reversing symmetry; each of these fixes a point and is therefore a reflection in a line. The finiteness of $\mathrm{Sym}(C)$ and the cyclicity of its direct subgroup, also in Lemma 3, are not part of this statement, and the note's standing assumption that $C$ is not a circle is not needed.
--
--   **Formalization Note**: $f$ is a real polynomial evaluated at $(\operatorname{Re}z,\operatorname{Im}z)$; irreducibility in $\mathbb{C}[x,y]$ is irreducibility of the image of $f$ under $\mathbb{R}[x,y]\to\mathbb{C}[x,y]$, and $\mathrm{Sym}(C)$ is the subgroup of the isometries `ℂ ≃ᵢ ℂ` preserving $C$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), Lemma 3, p. 2, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/IsometrySign.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
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

open CurveSymmetry
set_option autoImplicit false
open MvPolynomial

theorem CurveSymmetry.paper_isometry_sign {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (T : isometrySetGroup (cartesianLocus f)) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (∀ z : ℂ, eval (fun i : Fin 2 => if i = 0 then (T.val z).re else (T.val z).im) f =
        ε * eval (fun i : Fin 2 => if i = 0 then z.re else z.im) f) ∧
      ((∃ a b : ℂ, ∀ z : ℂ, T.val z = a * star z + b) → ε = 1) := by sorry
