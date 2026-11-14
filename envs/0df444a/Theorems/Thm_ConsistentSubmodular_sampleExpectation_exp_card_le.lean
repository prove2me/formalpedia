-- Prove2me | Theorems.Thm_ConsistentSubmodular_sampleExpectation_exp_card_le
-- name    : ConsistentSubmodular.sampleExpectation_exp_card_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:05.586196+00:00
-- url     : https://prove2.me/theorems/f8a96476-576e-4902-838a-a608556e85f7
-- title:
--   Exponential moment of the cardinality of an independent sample
-- statement:
--   Let $U$ be a finite set, $p:U\to[0,1]$, and let $S\subseteq U$ contain each $i\in U$ independently with probability $p_i$. Then for every real $s\ge 0$,
--
--   $$\mathbb E\big[e^{s|S|}\big]\;\le\;\exp\!\Big(\big(e^{s}-1\big)\sum_{i\in U}p_i\Big).$$
--
--   This is the moment-generating-function bound for a sum of independent indicators, and is the starting point of the cardinality tail bounds.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ExponentialTails.lean#L290-L324 (`ConsistentSubmodular.sampleExpectation_exp_card_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem ConsistentSubmodular.sampleExpectation_exp_card_le (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    sampleExpectation U p (fun S => Real.exp (s * S.card)) ≤
      Real.exp ((Real.exp s - 1) * ∑ i ∈ U, p i) := by sorry
