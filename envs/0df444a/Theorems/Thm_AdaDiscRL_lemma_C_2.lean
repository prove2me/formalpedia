-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_C_2
-- name    : AdaDiscRL.lemma_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:40.057999+00:00
-- url     : https://prove2.me/theorems/45ca678a-2b05-49da-a8a5-c4a2411e061d
-- title:
--   Lemma C.2 — concentration of the AdaMB reward estimates
-- statement:
--   Under Assumption 2, for a run of AdaMB: with probability at least $1-\delta$, for every episode $k\in[K]$, step $h$, active ball $B\in\mathcal P^k_h$ and $(x,a)\in B$,
--   $$
--   \big|\bar r^k_h(B)-r_h(x,a)\big|\le\mathrm{Rucb}^k_h(B)+4L_r\,\mathrm{diam}(B),\qquad \mathrm{Rucb}^k_h(B)=\sqrt{\frac{2\log(2HK^2/\delta)}{n^k_h(B)}} .
--   $$
--   The empirical reward of a ball is optimistic up to its bonus and a bias proportional to its diameter.
--
--   Differences from the source:
--   - reading: L_R → L_r; reason: the proof (p.41) and Assumption 2 use L_r
--   - generalization: AdaMB/AdaQL run with a given sequence of starting states {X_1^k}, action ã(B_h^k) (or a distribution on the ball), argmax with ties, rewards and transitions drawn from R_h and T_h → IsRun: starting states arbitrary random variables, action law any kernel supported on the ball's action cell, any argmax rule, only the conditional marginals of R_h^k and X_{h+1}^k fixed; reason: each choice of the source is a special case (reading R8); the statement holds for every such run
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma C.2, p.40

import Mathlib
import Definitions.Def_AdaDiscRL_adaMB
import Definitions.Def_AdaDiscRL_IsRun
import Definitions.Def_AdaDiscRL_Assumption2
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma C.2 (Concentration of Rewards for AdaMB)** (arXiv:2110.15843v3, p.40). Under
Assumption 2, for a run of AdaMB, with probability at least `1 − δ`, for every
`(h, k) ∈ [H] × [K]`, active ball `B ∈ P_h^k` and `(x, a) ∈ B`:
`|r̄_h^k(B) − r_h(x, a)| ≤ Rucb_h^k(B) + 4 L_r diam(B)`, `Rucb_h^k(B) = √(2 log(2HK²/δ)/n_h^k(B))`.

**Formalization Note.** `L_R` on the page is `L_r` (the proof, p.41, uses `L_r`). -/
theorem lemma_C_2 {S A ι : Type} [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S]
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
    (h2 : Assumption2 M D prm.Lr prm.LT)
    (hrun : IsRun M P choose play (statesMB P prm choose) prm.K μ traj) :
    1 - prm.δ ≤ (μ {ω | ∀ k ∈ Finset.Icc 1 prm.K, ∀ h : Fin H, ∀ B, isActive P (statesMB P prm choose (traj ω) k h) B →
      ∀ p ∈ P.region B,
        |(statesMB P prm choose (traj ω) k h).rbar B - M.meanReward h p| ≤ prm.rucbMB ((statesMB P prm choose (traj ω) k h).n B) + 4 * prm.Lr * P.diam B}).toReal := by sorry

end AdaDiscRL
