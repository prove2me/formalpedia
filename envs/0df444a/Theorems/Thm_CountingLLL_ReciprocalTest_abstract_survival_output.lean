-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_abstract_survival_output
-- name    : CountingLLL.ReciprocalTest.abstract_survival_output
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:40:45.365424+00:00
-- url     : https://prove2.me/theorems/39a852ca-6a47-4479-bbd5-dbc4c754e7de
-- title:
--   Suppressed-return product model has the reciprocal-test output probability
-- statement:
--   Suppose $0<B<1$ and $B\geq e^{-3/10}$. Form the paper’s independent initial Coin outcome, contracted absorbed walk, and independent uniform return tests at successive counter values. If $K$ is the final counter minus one, then one minus half the probability that all $K$ tests miss their designated values is exactly $1/(2B)$. This establishes the correctness calculation in the suppressed-return product model; coupling that model to the operational algorithm is a separate open theorem.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, correctness, p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
import Definitions.Def_CountingLLL_ReciprocalTest
open MeasureTheory CountingLLL.ContractedWalk CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.abstract_survival_output (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1)
    (hB : Real.exp (-(3/10 : ℝ)) ≤ B) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    let ν := (bitLaw (ENNReal.ofReal u)).prod (tapeLaw (ENNReal.ofReal θ))
    1 - (((ν.prod (Measure.infinitePi fun i : ℕ => uniformLaw (i+1)))
       {p : (Bool × Tape) × ((i : ℕ) → Fin (i+2)) |
          ∀ i < (if p.1.1 then 1 + upwardCount p.1.2 3 else upwardCount p.1.2 1),
            (p.2 i).val ≠ 0}).toReal)/2 = 1/(2*B) := by sorry
