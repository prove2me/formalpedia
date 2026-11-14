-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_execution_measurable
-- name    : CountingLLL.ReciprocalTest.execution_measurable
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:07:21.428913+00:00
-- url     : https://prove2.me/theorems/bf7bd309-b0c5-4cde-aa8c-98d4fd170d74
-- title:
--   ReciprocalTest execution events and oracle cost are measurable
-- statement:
--   For the small-step implementation of Algorithm 6, the termination event, each Boolean output event, and the extended-valued oracle-call cost are measurable. The cost is infinite on nonterminating entropy streams. Thus the probabilities and expected cost appearing in the formalized part of Lemma 6.5 are well-defined.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Algorithm 6 and Lemma 6.5, PDF pp. 26–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open MeasureTheory CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.execution_measurable : MeasurableSet {ω : Entropy | Halts ω} ∧ (∀ b : Bool, MeasurableSet {ω : Entropy | Returns ω b}) ∧ Measurable oracleCost := by sorry
