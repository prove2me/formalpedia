-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_contracted_up_probability
-- name    : CountingLLL.ReciprocalTest.contracted_up_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:18:37.076203+00:00
-- url     : https://prove2.me/theorems/cfd3ef8f-ea1c-40b4-9ed9-885f1c2ddaa0
-- title:
--   Contracted walk upward-step probability
-- statement:
--   Let independent calls to Coin return one with probability $u\in[0,1]$. In one walk iteration, two ones cause an upward change, a one followed by zero is a self-loop, and an initial zero causes a downward change. After suppressing any number of self-loops, the probability of an upward change is $u^2/(1-u+u^2)$. The theorem models the fresh Coin outcomes as IID Boolean pairs; the construction of the full recursive walk from the small-step machine remains separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.contracted_up_probability (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    let ν := (oracleLaw (ENNReal.ofReal (1-u))).prod (oracleLaw (ENNReal.ofReal (1-u)))
    let μ := Measure.infinitePi fun _ : ℕ => ν
    μ {ω : ℕ → Bool × Bool | ∃ n, (∀ i < n, ω i = (true,false)) ∧ ω n = (true,true)} =
      ENNReal.ofReal (u^2/(1-u+u^2)) := by sorry
