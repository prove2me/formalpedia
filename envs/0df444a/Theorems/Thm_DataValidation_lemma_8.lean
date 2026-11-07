-- Prove2me | Theorems.Thm_DataValidation_lemma_8
-- name    : DataValidation.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:54.985205+00:00
-- url     : https://prove2.me/theorems/67afb1d3-a790-45c7-a8a8-d7bf81e47928
-- title:
--   Lemma 8 — valid policies and obtainable sets
-- statement:
--   Let $I$ be a DVP instance.
--
--   1. For any valid probing policy, the set of successfully probed edges is obtainable, on every outcome of $\{\Omega_e\}$.
--   2. For any obtainable $R\subseteq E$ with $\tau(R)\le T$ and $p_e>0$ for every $e\in R$, there is a valid probing policy that successfully probes every edge of $R$ with non-zero probability.
--
--   Obtainability is therefore the essential static criterion for a set of edges to be removed.
--
--   **Formalization Note** "With non-zero probability" is stated as: there is a joint outcome $\omega$ of positive probability on which the policy probes every edge of $R$ successfully.
--
--   Differences from the source:
--   - reading: the policy must halt if τ_e > T for any unprobed edge e ∈ R(E) → a valid policy probes only unprobed edges of R(current E) that the leftover budget can pay for, and may stop at any time; reason: p.7 defines the probable edges as X(H,F,T) = R(H∪F) ∩ {e ∈ H : τ_e ≤ T}, so "any" means "every"; stopping early changes no optimum because w ≥ 0
--   - encoding: p_e ∈ [0,1] → p_e is rational, in [0,1]; reason: an instance must be written as a finite string; the hard instances have p ≡ 1
--   - encoding: w, τ, p are defined on E only → w, τ, p are total functions on vertex pairs that vanish off E; reason: normal form that excludes no instance and makes the code injective on valid instances
--   - encoding: vertices V, n := |V| → vertices Fin n; edges are pairs of vertices; reason: Lean convention; same instances
--   - encoding: W(π) is an expectation over independent Bernoulli variables → W(π) is the finite sum over joint outcomes ω of the product probability of ω times the reward on ω; reason: same number; the policy reads only the outcomes of edges it has probed
--   - encoding: successfully probes every edge in R with non-zero probability → there is a joint outcome of positive probability on which every edge of R is probed successfully; reason: the probability space is finite, so the two say the same
--   - encoding: any valid probing policy, randomized ones included (p.1: policies may sample random variables independent of {Ω_e}) → a deterministic history-dependent policy (Instance.Policy), each outcome ω; reason: a randomized policy is a seed-indexed family of valid deterministic policies (as in Instance.IsPolicyReward); on each seed and outcome its successful probes are those of one deterministic policy, and part 2 asks only for existence
--   - generalization: a probing budget T ∈ N = {1, 2, …} (p.1, in the sentence that writes w_e, τ_e ∈ N₀) → any T ∈ ℕ, including T = 0; reason: the statement holds verbatim at T = 0; on T ≥ 1 it is the page's statement
-- source:
--   Tinguely, van der Heijden, Approximation and Hardness for the Data Validation Problem, arXiv:2611.06773 (sha256 6595f819…), Lemma 8, p.6

import Definitions.Def_DataValidation_Obtainable
import Definitions.Def_DataValidation_Policy

set_option autoImplicit false

namespace DataValidation

/-- **Lemma 8** of arXiv:2611.06773 (sha256 6595f819…), p.6. For any valid probing policy, the set of
successfully probed edges is obtainable, on every outcome. Conversely, for any obtainable `R ⊆ E` with
`τ(R) ≤ T` and `p_e > 0` on `R`, there is a valid policy and an outcome of positive probability on
which it probes every edge of `R` successfully. -/
theorem lemma_8 (I : Instance) (hI : I.IsValid) :
    (∀ π : I.Policy, Instance.IsValidPolicy π → ∀ ω : I.Outcome,
      Obtainable I.E (Instance.successes (Instance.finalHistory π ω))) ∧
    (∀ R : Finset I.Edge, Obtainable I.E R → ∑ e ∈ R, I.τ e ≤ I.T → (∀ e ∈ R, 0 < I.p e) →
      ∃ π : I.Policy, Instance.IsValidPolicy π ∧ ∃ ω : I.Outcome,
        0 < Instance.outcomeProb ω ∧ R ⊆ Instance.successes (Instance.finalHistory π ω)) := by sorry

end DataValidation
