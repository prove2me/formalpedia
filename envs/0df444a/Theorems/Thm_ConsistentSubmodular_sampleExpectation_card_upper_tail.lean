-- Prove2me | Theorems.Thm_ConsistentSubmodular_sampleExpectation_card_upper_tail
-- name    : ConsistentSubmodular.sampleExpectation_card_upper_tail
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:58.659278+00:00
-- url     : https://prove2.me/theorems/382f85f6-bebf-4f6a-8dee-85a477099e99
-- title:
--   Additive upper tail for the cardinality of an independent sample
-- statement:
--   Let $U$ be a finite set, $p:U\to[0,1]$, and let $S\subseteq U$ contain each $i$ independently with probability $p_i$. Let $\kappa,b\in\mathbb R$ with $\sum_{i\in U}p_i\le\kappa$ and $0<b\le 2\kappa$. Then
--
--   $$\Pr\big[\,|S|>\kappa+b\,\big]\;\le\;\exp\!\Big(-\frac{b^2}{4\kappa}\Big).$$
--
--   An independent sample of expected size at most $\kappa$ therefore exceeds $\kappa+b$ with probability at most $e^{-b^2/(4\kappa)}$. This additive cardinality tail is used to bound the size of the rounded sets in the joint rounding.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ExponentialTails.lean#L326-L361 (`ConsistentSubmodular.sampleExpectation_card_upper_tail`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem ConsistentSubmodular.sampleExpectation_card_upper_tail (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {κ b : ℝ} (hmass : ∑ i ∈ U, p i ≤ κ)
    (hb : 0 < b) (hb2 : b ≤ 2 * κ) :
    sampleExpectation U p (fun S => if κ + b < (S.card : ℝ) then 1 else 0) ≤
      Real.exp (-(b ^ 2) / (4 * κ)) := by sorry
