-- Prove2me | Theorems.Thm_DelayDep_Equiv_exo_law_determined
-- name    : DelayDep.Equiv.exo_law_determined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:21.879087+00:00
-- url     : https://prove2.me/theorems/37d404f3-4a3a-46b0-a6eb-5a18854c9f38
-- title:
--   Proof of Theorem 1, p. 3349 — the law of X^ex is uniquely determined by f^ex, given the arrivals and n
-- statement:
--   Let $f$ be a joint pdf on $\mathbb R_+^2$ and $n \ge 1$. Let $E_1$ and $E_2$ be two systems with exogenous dependence $f$ and $n$ servers, on probability spaces $(\Omega,P)$ and $(\Omega',P')$, whose interarrival sequences and initial residual service times have the same joint law. Then the processes $X^{ex,1}$ and $X^{ex,2}$ have the same law,
--   $$\mathcal L\big((X^{ex,1}(t))_{t\ge0}\big) = \mathcal L\big((X^{ex,2}(t))_{t\ge0}\big),$$
--   and both path maps are almost-everywhere measurable.
--
--   This makes $\mathcal L^{ex}(A, n; f^{ex})$ well defined; the proof of Theorem 1 uses it to transfer the law of the coupled system to every exogenous system.
--
--   **Formalization Note** Inputs and initial state as in the model file (empty queue at time $0$). Measurability of the path maps is part of the conclusion.
-- source:
--   Wu, Bassamboo & Perry, When service times depend on customers’ delays, Operations Research 70(6) (2022), p. 3349 (PDF 6), proof of Theorem 1, "Because the law of the process X^ex is uniquely determined by f^ex …"

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

namespace DelayDep.Equiv

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 1, p. 3349: the law of `X^ex` is uniquely determined by `f^ex`, given the
arrivals and `n`. Two exogenous systems with the same joint pdf `f` and the same joint law of
interarrival times and initial residual service times have the same law of the path
`t ↦ X^ex(t)`. -/
theorem exo_law_determined (f : ℝ → ℝ → ℝ) (hf : IsJointPdf f)
    (n : ℕ) [NeZero n] (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (E₁ : ExoSystem n f P) (E₂ : ExoSystem n f P')
    (h_input : E₁.inputLaw P = E₂.inputLaw P') :
    AEMeasurable E₁.path P ∧ AEMeasurable E₂.path P' ∧ P.map E₁.path = P'.map E₂.path := by sorry

end DelayDep.Equiv
