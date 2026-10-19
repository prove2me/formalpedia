-- Prove2me | Theorems.Thm_DelayDep_Equiv_lemma_1_sufficiency
-- name    : DelayDep.Equiv.lemma_1_sufficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:59.975026+00:00
-- url     : https://prove2.me/theorems/3ec79d6b-c99c-40f9-a8a7-75734ee928a3
-- title:
--   Lemma 1 (sufficiency), p. 3350, proof p. 3353 — the law of X^en is determined by (f_T, ψ), given the arrivals and n
-- statement:
--   Let $f_T$ be a patience pdf on $[0,\infty)$ and $\psi$ a conditional service-time pdf, i.e. $\psi(\cdot,z)$ is a pdf on $[0,\infty)$ for every $z \ge 0$ with $\int_z^\infty f_T > 0$. Let $n \ge 1$, and let $N_1$ and $N_2$ be two systems with endogenous dependence $(f_T, \psi)$ and $n$ servers, on probability spaces $(\Omega, P)$ and $(\Omega', P')$, whose interarrival sequences and initial residual service times have the same joint law. Then the processes $X^{en,1}$ and $X^{en,2}$ have the same law:
--   $$\mathcal L\big((X^{en,1}(t))_{t \ge 0}\big) = \mathcal L\big((X^{en,2}(t))_{t \ge 0}\big),$$
--   and both path maps are almost-everywhere measurable.
--
--   This is the "if" direction of Lemma 1: $\mathcal L^{en}(A, n; f_T, \psi)$ is well defined, depending on the system only through $(f_T,\psi)$, the arrivals and the initial state. The proof of Theorem 1 uses it when it moves the endogenous system to a new probability space.
--
--   **Formalization Note** The paper's "any arrival process $A$ … and initial condition $X^{en}(0)$" is the joint law of the interarrival sequence and the initial residual service times (empty queue at time $0$). The path maps' measurability is a conclusion, so that the equality of image measures is not an artefact of Lean's convention that the image under a non-measurable map is $0$.
-- source:
--   Wu, Bassamboo & Perry, When service times depend on customers’ delays, Operations Research 70(6) (2022), p. 3350 (PDF 7), Lemma 1 ("if" direction); proof p. 3353 (PDF 10), Appendix B

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

namespace DelayDep.Equiv

open MeasureTheory ProbabilityTheory

/-- Lemma 1 (sufficiency), p. 3350, proof p. 3353: the law of `X^en` is determined by
`(f_T, ψ)`, given the arrivals and `n`. Two endogenous systems with the same patience pdf `fT`,
the same conditional service-time pdf `ψ` and the same joint law of interarrival times and initial
residual service times have the same law of the path `t ↦ X^en(t)`. -/
theorem lemma_1_sufficiency (fT : ℝ → ℝ) (ψ : ℝ → ℝ → ℝ) (hfT : IsPdf fT)
    (hψ : ∀ z : ℝ, 0 ≤ z → 0 < ∫ y in Set.Ioi z, fT y → IsPdf (fun x => ψ x z))
    (n : ℕ) [NeZero n] (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (N₁ : EndoSystem n fT ψ P) (N₂ : EndoSystem n fT ψ P')
    (h_input : N₁.inputLaw P = N₂.inputLaw P') :
    AEMeasurable N₁.path P ∧ AEMeasurable N₂.path P' ∧ P.map N₁.path = P'.map N₂.path := by sorry

end DelayDep.Equiv
