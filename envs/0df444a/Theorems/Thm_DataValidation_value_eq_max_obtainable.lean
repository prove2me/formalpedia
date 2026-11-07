-- Prove2me | Theorems.Thm_DataValidation_value_eq_max_obtainable
-- name    : DataValidation.value_eq_max_obtainable
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:27.429309+00:00
-- url     : https://prove2.me/theorems/d2fc5654-7b2e-4285-83bc-fcfd36df37e6
-- title:
--   Proof of Theorem 1, p.4 (corrected: weighted objective $W(\pi)$) — at $p\equiv1$, the value is the maximum over obtainable sets
-- statement:
--   Let $I$ be a valid DVP instance with $p_e=1$ on $E$. Then the optimal value over all valid policies, randomized ones included, is attained and equals
--
--   $$\operatorname{value}(I)=\max\{w(R): R\subseteq E\text{ obtainable},\ \tau(R)\le T\}.$$
--
--   This is what lets the proof of Theorem 1 speak of "the optimal solution OPT (the edges in $E_H$ removed by an optimal policy)" as a set of edges.
--
--   Differences from the source:
--   - correction: W(π) := E[∑_e 1{π successfully probes e}], with no weight in the display on p.1 → W(π) = E[∑_e w_e 1{π successfully probes e}]; reason: the display contradicts "we collect w_e as a reward" on the same page and Lemma 11 on p.7; with the printed formula, H edgeless on 3 vertices, k = 2, T = 3 scores 3 ≥ C(2,2) by probing three q-edges although H has no 2-clique
--   - reading: the policy must halt if τ_e > T for any unprobed edge e ∈ R(E) → a valid policy probes only unprobed edges of R(current E) that the leftover budget can pay for, and may stop at any time; reason: p.7 defines the probable edges as X(H,F,T) = R(H∪F) ∩ {e ∈ H : τ_e ≤ T}, so "any" means "every"; stopping early changes no optimum because w ≥ 0
--   - encoding: policies may sample random variables independent of {Ω_e} → a randomized policy is a probability space of seeds with a valid deterministic policy for each seed, and its reward is the integral of W over the seeds; reason: a policy that samples adaptively can hold all its draws in the seed; same set of rewards
--   - encoding: p_e ∈ [0,1] → p_e is rational, in [0,1]; reason: an instance must be written as a finite string; the hard instances have p ≡ 1
--   - encoding: w, τ, p are defined on E only → w, τ, p are total functions on vertex pairs that vanish off E; reason: normal form that excludes no instance and makes the code injective on valid instances
--   - encoding: vertices V, n := |V| → vertices Fin n; edges are pairs of vertices; reason: Lean convention; same instances
--   - encoding: W(π) is an expectation over independent Bernoulli variables → W(π) is the finite sum over joint outcomes ω of the product probability of ω times the reward on ω; reason: same number; the policy reads only the outcomes of edges it has probed
--   - encoding: arg max over policies π of W(π) → the real supremum of the rewards of valid policies; reason: the set of rewards is nonempty and bounded above by the sum of the weights, so the supremum is a true one
--   - generalization: OPT for the DVP instance G_H → every valid instance with p ≡ 1 on E; reason: G_H is such an instance, so this specializes to the page's use
--   - generalization: a probing budget T ∈ N = {1, 2, …} (p.1, in the sentence that writes w_e, τ_e ∈ N₀) → any T ∈ ℕ, including T = 0; reason: the statement holds verbatim at T = 0; on T ≥ 1 it is the page's statement
-- source:
--   Tinguely, van der Heijden, Approximation and Hardness for the Data Validation Problem, arXiv:2611.06773 (sha256 6595f819…), proof of Theorem 1, p.4

import Definitions.Def_DataValidation_Obtainable
import Definitions.Def_DataValidation_value

set_option autoImplicit false

namespace DataValidation

/-- arXiv:2611.06773 (sha256 6595f819…), proof of Theorem 1, p.4: "OPT is the optimal solution (the
edges in E_H removed by an optimal policy)". On a valid instance with `p ≡ 1` on `E`, the optimal value
over all valid policies, randomized ones included, is the maximum of `w(R)` over the obtainable sets `R`
with `τ(R) ≤ T`. -/
theorem value_eq_max_obtainable (I : Instance) (hI : I.IsValid) (hp : ∀ e ∈ I.E, I.p e = 1) :
    IsGreatest ((fun R : Finset I.Edge => ((∑ e ∈ R, I.w e : ℕ) : ℝ)) ''
      {R | Obtainable I.E R ∧ ∑ e ∈ R, I.τ e ≤ I.T}) I.value := by sorry

end DataValidation
