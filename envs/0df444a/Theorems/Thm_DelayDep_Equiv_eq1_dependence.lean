-- Prove2me | Theorems.Thm_DelayDep_Equiv_eq1_dependence
-- name    : DelayDep.Equiv.eq1_dependence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:03.823359+00:00
-- url     : https://prove2.me/theorems/16b4fcc8-edbd-4221-a35c-1f530fed18b6
-- title:
--   Theorem 1, eq. (1), p. 3348 — f^ex_T is a pdf and ψ^en(·, z) of (1) is a pdf wherever the patience tail is positive
-- statement:
--   Let $f$ be a joint probability density on $\mathbb R_+^2$ of (service time, patience time). Its patience marginal is $f^{ex}_T(y) = \int_0^\infty f(x,y)\,dx$, its patience tail is $\bar F^{ex}_T(z) = \int_z^\infty f^{ex}_T(y)\,dy$, and formula (1) of the paper defines
--   $$\psi^{en}(x,z) = \frac{\int_z^\infty f(x,y)\,dy}{\int_z^\infty f^{ex}_T(y)\,dy}.$$
--   Then
--
--   1. $f^{ex}_T$ is a probability density on $[0,\infty)$;
--   2. for every $z \ge 0$ with $\bar F^{ex}_T(z) > 0$, the function $x \mapsto \psi^{en}(x,z)$ is a probability density on $[0,\infty)$.
--
--   This is the half of Theorem 1 asserting that (1) defines an endogenous dependence: a patience pdf together with a conditional service-time pdf at each offered wait.
--
--   **Formalization Note** At $z$ with $\bar F^{ex}_T(z) = 0$ the quotient in (1) is $0/0$ (and $0$ in Lean); a customer meeting such an offered wait abandons almost surely, so no service-time law is needed there.
-- source:
--   Wu, Bassamboo & Perry, When service times depend on customers’ delays, Operations Research 70(6) (2022), p. 3348 (PDF 5), Theorem 1, eq. (1)

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

namespace DelayDep.Equiv

open MeasureTheory

/-- Theorem 1, eq. (1), p. 3348: for a joint pdf `f` on ℝ²₊, the patience marginal `f^ex_T` is a
pdf on `[0, ∞)`, and for every `z ≥ 0` with `∫_z^∞ f^ex_T > 0` the function
`x ↦ ψ^en(x, z)` of (1) is a pdf on `[0, ∞)`. -/
theorem eq1_dependence (f : ℝ → ℝ → ℝ) (hf : IsJointPdf f) :
    IsPdf (fTex f) ∧
      ∀ z : ℝ, 0 ≤ z → 0 < tailT f z → IsPdf (fun x => psiEn f x z) := by sorry

end DelayDep.Equiv
