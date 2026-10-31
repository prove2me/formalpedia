-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_C_1
-- name    : AdaDiscRL.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:13.033113+00:00
-- url     : https://prove2.me/theorems/86f9ffb4-08bc-43be-9f14-1c1af65a6860
-- title:
--   Lemma C.1 — concentration of the weighted reward averages
-- statement:
--   For a run of AdaQL or AdaMB, every $\delta\in(0,1)$ and every deterministic weight array $(\alpha^i_t)$: with probability at least $1-\delta$, simultaneously for all episodes $k\in[K]$, steps $h$ and active balls $B\in\mathcal P^k_h$, with $k_1<\dots<k_t\le k$ the episodes at which $B$ or its ancestors were selected at step $h$,
--   $$
--   \Big|\sum_{i=1}^t\alpha^i_t\big(R^{k_i}_h-r_h(X^{k_i}_h,A^{k_i}_h)\big)\Big|\le\sqrt{2\sum_{i=1}^t(\alpha^i_t)^2\log(2HK^2/\delta)} .
--   $$
--   With $\alpha^i_t=1/t$ (AdaMB) or the weights of Eq. (11) (AdaQL) the right side is at most the reward bonus Rucb.
--
--   Differences from the source:
--   - reading: for all (x, a, h, k) … with probability at least 1 − δ → with probability at least 1 − δ, simultaneously for all h, k ∈ [K] and active balls B; reason: the proof takes a union bound to obtain the simultaneous event, which later lemmas use; the pointwise reading is weaker
--   - encoding: the condition (x, a) ∈ B for some B ∈ P_h^k → dropped; the bound is stated for every active ball B; reason: the inequality does not involve (x, a)
--   - generalization: δ the algorithm's confidence parameter → any δ ∈ (0, 1), independent of the algorithm's δ; reason: the source's case is δ = prm.δ
--   - generalization: AdaMB/AdaQL run with a given sequence of starting states {X_1^k}, action ã(B_h^k) (or a distribution on the ball), argmax with ties, rewards and transitions drawn from R_h and T_h → IsRun: starting states arbitrary random variables, action law any kernel supported on the ball's action cell, any argmax rule, only the conditional marginals of R_h^k and X_{h+1}^k fixed; reason: each choice of the source is a special case (reading R8); the statement holds for every such run
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma C.1, p.39

import Mathlib
import Definitions.Def_AdaDiscRL_adaMB
import Definitions.Def_AdaDiscRL_IsRun
import Definitions.Def_AdaDiscRL_encounters
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma C.1 (Concentration of Rewards)** (arXiv:2110.15843v3, p.39). For a run of AdaQL or
AdaMB, every `δ ∈ (0, 1)` and every deterministic weight family `(α_t^i)`, with probability at least
`1 − δ`, simultaneously for all `(h, k) ∈ [H] × [K]` and active balls `B ∈ P_h^k` (with
`t = n_h^k(B)` and `k₁ < ⋯ < k_t ≤ k` the episodes at which `B` or its ancestors were selected at
step `h`):
`|Σ_{i=1}^t α_t^i (R_h^{k_i} − r_h(X_h^{k_i}, A_h^{k_i}))| ≤ √(2 Σ_{i=1}^t (α_t^i)² log(2HK²/δ))`.

**Formalization Note.** The event is simultaneous in `(h, k, B)` (the proof's union bound; the
pointwise reading would be weaker). The weights are any real array `w t i`; the confidence `δ` is
independent of the algorithm's `δ`. -/
theorem lemma_C_1 {S A ι : Type} [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S]
    [BorelSpace S] [MetricSpace A] [CompactSpace A] [Nonempty A] [MeasurableSpace A]
    [BorelSpace A]
    (D : S × A → S × A → ℝ) {H : ℕ} (prm : AdaParams H)
    (P : HierPartition S A ι D prm.dS prm.K) (choose : Finset ι → (ι → ℝ) → ι)
    (hD : IsAdmissibleMetric D) (hH : 1 ≤ H) (hK : 1 ≤ prm.K) (hδ0 : 0 < prm.δ) (hδ1 : prm.δ < 1)
    (hLr : 0 ≤ prm.Lr) (hLV : 0 ≤ prm.LV) (hLT : 0 ≤ prm.LT)
    (hv0 : ∀ h : Fin H, (H : ℝ) - h ≤ prm.v0 h ∧ prm.v0 h ≤ H)
    (hchoose : IsArgmaxRule choose)
    (M : EpisodicMDP S A H) (play : ι → Kernel S A)
    (hplay : ∀ B, IsMarkovKernel (play B))
    (hplay_supp : ∀ B x, x ∈ P.sCell B → play B x (P.aCell B)ᶜ = 0)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (traj : Ω → ℕ → EpData S A H)
    (alg : (ℕ → EpData S A H) → ℕ → AlgState S ι H)
    (halg : alg = statesQL P prm choose ∨ alg = statesMB P prm choose)
    (hrun : IsRun M P choose play alg prm.K μ traj)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1) (w : ℕ → ℕ → ℝ) :
    1 - δ ≤ (μ {ω | ∀ k ∈ Finset.Icc 1 prm.K, ∀ h : Fin H, ∀ B,
      isActive P (alg (traj ω) k h) B →
      |∑ i : Fin (encounters P choose alg (traj ω) k h B).card, w (encounters P choose alg (traj ω) k h B).card (i.val + 1) *
          ((traj ω (encEp P choose alg (traj ω) k h B i)).2.2 h - M.meanReward h ((traj ω (encEp P choose alg (traj ω) k h B i)).1 h.castSucc, (traj ω (encEp P choose alg (traj ω) k h B i)).2.1 h))| ≤
        Real.sqrt (2 * ∑ i : Fin (encounters P choose alg (traj ω) k h B).card, (w (encounters P choose alg (traj ω) k h B).card (i.val + 1)) ^ 2 * Real.log (2 * H * (prm.K : ℝ) ^ 2 / δ))}).toReal := by sorry

end AdaDiscRL
