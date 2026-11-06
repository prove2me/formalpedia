-- Prove2me | Theorems.Thm_BorelRobustMDP_lemma_2_4
-- name    : BorelRobustMDP.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:27.95781+00:00
-- url     : https://prove2.me/theorems/74e80812-06bb-443a-8cf6-1167d611ba71
-- title:
--   Lemma 2.4 — a decision rule of nature induces a stochastic kernel
-- statement:
--   For $n=0,\dots,N-1$, a decision rule $\gamma_n:\mathcal H_n\times A\to\mathcal Q_{n+1}$, measurable for the Borel σ-algebra of the weak* topology, induces a stochastic kernel from $\mathcal H_n\times A$ to the disturbance space by
--
--   $$\gamma_n(B\mid h_n,a_n):=\gamma_n(h_n,a_n)(B).$$
--
--   This is what makes the transition law $Q_n^\gamma$ of (2.3) a kernel.
--
--   Differences from the source:
--   - encoding: decision rule γ_n : 𝓗_n × A → 𝒬_{n+1}, and Markov rule γ_n : D_n → 𝒬_{n+1} → measurable maps on Hist E A n × A and on E × A, into the type R.Amb (n + 1); reason: the proof of Lemma 2.4, p.24, uses this measurability; a rule extends by a constant from a measurable set
--   - encoding: feasible histories 𝓗_n, with policies and rules of nature defined on them → the raw history space Hist E A n with the predicate Feasible; kernels and rules are defined on raw histories, and statements are at feasible ones; reason: 𝓗_n is measurable, so kernels and rules extend, and a path from a feasible history stays feasible almost surely
--   - encoding: σ(L^q, L^p) on the densities 𝒬_n^d and its Borel σ-algebra → the topology on 𝒬_n induced by Q ↦ ∫ f dQ for f ∈ L^p(P_n), with borel of it; weak* closed means closed in this topology on 𝓜^q(P_n); reason: ∫ f dQ = E[f dQ/dP_n], and 𝓜^q(P_n) is weak* closed in L^q, so these are the same notions; no Lp–Lq duality is needed to state them
--   - encoding: stages n = 0, …, N − 1 and ambiguity sets n = 1, …, N → ℕ-indexed families used at n < N and at 1 ≤ n ≤ N, and Fin N for the rules of a policy; N = 0 is not excluded; reason: the other indices are unused, and N = 0 is a harmless empty case
--   - generalization: E and A Borel spaces (standing, p.3) → E and A arbitrary measurable spaces; reason: the statement and its proof (p.24) concern measurability only; Borel spaces are a special case
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, Lemma 2.4, p.5; proof p.24

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_RobustModel

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (Hist)

namespace BorelRobustMDP

universe u v

/-- Lemma 2.4 (Bäuerle & Glauner, arXiv:2007.13103v1, p.5; proof p.24). A decision rule
`γ_n : 𝓗_n × A → 𝒬_{n+1}` of nature, measurable for the Borel σ-algebra of the weak* topology,
induces a stochastic kernel by `γ_n(B | h_n, a_n) := γ_n(h_n, a_n)(B)`. -/
theorem lemma_2_4 {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] {N : ℕ} (R : RobustModel E A Z N) (n : ℕ) (hn : n < N)
    (g : Hist E A n × A → R.Amb (n + 1)) (hg : Measurable g) :
    ∃ κ : Kernel (Hist E A n × A) Z, IsMarkovKernel κ ∧ ∀ y, κ y = (g y).measure := by sorry

end BorelRobustMDP
