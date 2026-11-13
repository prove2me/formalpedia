-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_fair_independent_tape
-- name    : CountingLLL.RandomRAM.fair_independent_tape
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:00:46.842168+00:00
-- url     : https://prove2.me/theorems/8b243571-8383-4f12-9e69-b6f1fda50a3c
-- title:
--   The random RAM tape consists of independent fair bits
-- statement:
--   The random tape of the fair-bit CSP oracle RAM consists of mutually independent unbiased bits: for every coordinate, both outcomes have probability 1/2. This validates the probability source used to formulate the randomized counting and exact sampling theorems.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, Section 2.5 (PDF p.8), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_RandomRAM
open MeasureTheory
open scoped ENNReal

theorem CountingLLL.RandomRAM.fair_independent_tape : (∀ i : ℕ, ∀ b : Bool, CountingLLL.RandomRAM.tapeMeasure {ω | ω i = b} = (1 / 2 : ℝ≥0∞)) ∧ ProbabilityTheory.iIndepFun (fun i (ω : CountingLLL.RandomRAM.Tape) => ω i) CountingLLL.RandomRAM.tapeMeasure := by sorry
