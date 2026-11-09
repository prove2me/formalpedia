-- Prove2me | Theorems.Thm_BSCvsBEC_theorem_2_12
-- name    : BSCvsBEC.theorem_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:33:27.917816+00:00
-- url     : https://prove2.me/theorems/db16a6c0-6133-4743-9e46-ac91f411eae6
-- title:
--   Theorem 2.12 (Heinävaara): every Hermitian pair has a tracial joint spectral measure
-- statement:
--   Let $A,B\in\mathbb C^{n\times n}$ be Hermitian. There exists a (positive) measure $\mu=\mu_{A,B}$ on $\mathbb R^2$ such that the following holds. For every measurable $f$ on $\mathbb R$ with $f(0)=0$ and $\int_{-M}^M|f(t)/t|\,dt<\infty$ for every $M>0$, let
--   $$H(f)(x):=\int_0^1\frac{1-t}{t}\,f(xt)\,dt.$$
--   Then for any $x,y\in\mathbb R$,
--   $$\operatorname{Tr}H(f)(xA+yB)=\int_{\mathbb R^2}f(xa+yb)\,d\mu(a,b).$$
--
--   This is Theorem 6 of Heinävaara [Hei24], cited by the paper; it lets traces of functions of $xA+yB$ be computed as integrals of scalar functions of $xa+yb$, which is how the paper lifts scalar inequalities to matrices.
--
--   Differences from the source:
--   - reading: Tr H(f)(xA + yB) = ∫ f(xa + yb) dμ (58) → (a, b) ↦ f(xa + yb) is μ-integrable and the integral equals the trace; reason: the integral in (58) must exist for the equation to be meaningful; applying (58) to |f| (also admissible) shows ∫|f(xa+yb)| dμ = Tr H(|f|)(xA+yB) < ∞, so the reading adds nothing
--   - encoding: A, B ∈ ℂ^{n×n} → Matrix ι ι ℂ for a finite type ι; reason: Lean convention; same instances up to reindexing
--   - encoding: ∫_{−M}^{M} |f(t)/t| dt < ∞ → t ↦ f(t)/t integrable on [−M, M]; reason: Lean convention for a finite Lebesgue integral of a measurable function
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 2.12 (Theorem 6 in [Hei24]), eqs. (57)–(58), pp.11–12

import Mathlib
import Definitions.Def_BSCvsBEC_IsTJSM

open MeasureTheory

namespace BSCvsBEC

/-- **Theorem 2.12 (pp.11–12; Theorem 6 in [Hei24], Heinävaara).** Let `A, B` be Hermitian matrices.
There exists a (positive) measure `μ = μ_{A,B}` on `ℝ²` such that for every measurable `f` on `ℝ`
with `f(0) = 0` and `∫_{−M}^{M} |f(t)/t| dt < ∞` for every `M > 0`, and for any `x, y ∈ ℝ`,
`Tr H(f)(xA + yB) = ∫_{ℝ²} f(xa + yb) dμ(a, b)` (eq. (58)), where
`H(f)(x) := ∫₀¹ ((1 − t)/t) f(xt) dt` (eq. (57)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 2.12, pp.11–12.

**Formalization Note.** `ℂ^{n×n}` is `Matrix ι ι ℂ` for a finite type `ι`. The measure is chosen
before `f`, `x`, `y` (it depends on `A`, `B` only). Equation (58) is read as integrability of
`(a, b) ↦ f(xa + yb)` together with the equality (`IsTJSM`). -/
theorem theorem_2_12 (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ μ : Measure (ℝ × ℝ), IsTJSM A B μ := by sorry

end BSCvsBEC
