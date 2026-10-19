-- Prove2me | Theorems.Thm_DelayDep_Equiv_theorem_1
-- name    : DelayDep.Equiv.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:09.745001+00:00
-- url     : https://prove2.me/theorems/c5ee8e60-5c59-47a3-bc65-089938e5f851
-- title:
--   Theorem 1, p. 3348 — every exogenous dependence f^ex has the equivalent endogenous dependence (1): the queue processes X^ex and X^en have the same law
-- statement:
--   Consider an $n$-server first-come-first-served queue with abandonment. Let $f$ be a joint probability density on $\mathbb R_+^2$ of (service time, patience time) — an **exogenous dependence**. Define the **endogenous dependence** $(f^{en}_T, \psi^{en})$ by formula (1):
--   $$f^{en}_T(z) = f^{ex}_T(z) \quad\text{and}\quad \psi^{en}(x,z) = \frac{\int_z^\infty f(x,y)\,dy}{\int_z^\infty f^{ex}_T(y)\,dy},$$
--   where $f^{ex}_T(y) = \int_0^\infty f(x,y)\,dx$. Then
--
--   1. $f^{en}_T$ is a probability density on $[0,\infty)$;
--   2. $\psi^{en}(\cdot,z)$ is a probability density on $[0,\infty)$ for every $z \ge 0$ with $\int_z^\infty f^{ex}_T > 0$;
--   3. $f$ is **equivalent** to $(f^{en}_T,\psi^{en})$: for every $n \ge 1$, every system with exogenous dependence $f$ and every system with endogenous dependence $(f^{en}_T,\psi^{en})$, on any probability spaces, whose arrival sequences and initial states have the same joint law, the queue processes have the same law,
--   $$\mathcal L^{ex}(A, n; f^{ex}) = \mathcal L^{en}(A, n; f^{en}_T, \psi^{en}).$$
--
--   This is the main result of the paper: every exogenous service–patience dependence can be replaced, for all purposes concerning the law of the queueing dynamics, by a dependence of the service time on the delay the customer experiences.
--
--   **Formalization Note** The law of $X = (Y, Q, U, V, B)$ is the law of the path $t \mapsto X(t)$ on `NNReal → State n` with the product σ-algebra; measurability of both path maps is part of the conclusion. Relative to the page: the queue is empty at time $0$ (arbitrary initial residual service times); arrivals have positive interarrival times whose sums tend to infinity; the service-time law of the endogenous system is prescribed only at offered waits with positive patience tail (elsewhere the customer abandons a.s.); Assumption 1 (differentiability of $\Psi^{en}$) is not imposed, since the $\psi^{en}$ of (1) need not satisfy it for a general $f$ and the theorem's proof does not use it. Customers are 0-based.
-- source:
--   Wu, Bassamboo & Perry, When service times depend on customers’ delays, Operations Research 70(6) (2022), p. 3348 (PDF 5), Theorem 1

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

namespace DelayDep.Equiv

open MeasureTheory

/-- Theorem 1, p. 3348: for every exogenous dependence with joint pdf `f` on ℝ²₊, formula (1)
— `f^en_T = f^ex_T` and `ψ^en(x, z) = ∫_z^∞ f(x, y) dy / ∫_z^∞ f^ex_T(y) dy` — defines an
endogenous dependence (a patience pdf, and a service-time pdf at every offered wait `z ≥ 0` with
positive patience tail), and this endogenous dependence is equivalent to `f`. -/
theorem theorem_1 (f : ℝ → ℝ → ℝ) (hf : IsJointPdf f) :
    IsPdf (fTex f) ∧
      (∀ z : ℝ, 0 ≤ z → 0 < tailT f z → IsPdf (fun x => psiEn f x z)) ∧
      IsEquivalent f (fTex f) (psiEn f) := by sorry

end DelayDep.Equiv
