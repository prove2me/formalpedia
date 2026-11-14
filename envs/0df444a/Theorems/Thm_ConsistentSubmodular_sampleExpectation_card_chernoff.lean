-- Prove2me | Theorems.Thm_ConsistentSubmodular_sampleExpectation_card_chernoff
-- name    : ConsistentSubmodular.sampleExpectation_card_chernoff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:33.027785+00:00
-- url     : https://prove2.me/theorems/75b5491b-6929-4dd3-bcfc-3fb34300adbc
-- title:
--   Equation (38) — multiplicative Chernoff bound for the cardinality of an independent sample
-- statement:
--   Let $U$ be a finite set, $p:U\to[0,1]$, and let $S\subseteq U$ contain each $i$ independently with probability $p_i$. Let $\kappa,\eta\in\mathbb R$ with $\sum_{i\in U}p_i\le\kappa$ and $0<\eta\le 1$. Then
--
--   $$\Pr\big[\,|S|>(1+\eta)\kappa\,\big]\;\le\;\exp\!\Big(-\frac{\eta^2\kappa}{3}\Big).$$
--
--   This is the multiplicative Chernoff bound (38). It follows from the exponential moment of $|S|$ taken at $s=\eta-\eta^2/3$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ExponentialTails.lean#L373-L411 (`ConsistentSubmodular.sampleExpectation_card_chernoff`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem ConsistentSubmodular.sampleExpectation_card_chernoff (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {κ η : ℝ} (hmass : ∑ i ∈ U, p i ≤ κ)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    sampleExpectation U p (fun S => if (1 + η) * κ < (S.card : ℝ) then 1 else 0) ≤
      Real.exp (-(η ^ 2) * κ / 3) := by sorry
