-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_C_3
-- name    : AdaDiscRL.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:15.720992+00:00
-- url     : https://prove2.me/theorems/f882ddc6-44d7-4c92-862f-eda3bfde3d1b
-- title:
--   Lemma C.3 — concentration of the AdaQL transition terms
-- statement:
--   Under Assumption 1, for a run of AdaQL, every $\delta\in(0,1)$ and every deterministic weight array $(\alpha^i_t)$: with probability at least $1-\delta$, simultaneously for all $k\in[K]$, steps $h$ and active balls $B\in\mathcal P^k_h$ (with $t$ and $k_i$ as in Lemma C.1),
--   $$
--   \Big|\sum_{i=1}^t\alpha^i_t\Big(V^\star_{h+1}(X^{k_i}_{h+1})-\mathbb E_{Y\sim T_h(\cdot\mid X^{k_i}_h,A^{k_i}_h)}\big[V^\star_{h+1}(Y)\big]\Big)\Big|\le H\sqrt{2\sum_{i=1}^t(\alpha^i_t)^2\log(2HK^2/\delta)} .
--   $$
--   Moreover, for the weights of Eq. (11) and every $t\ge1$ the right-hand side is at most $\mathrm{Tucb}=2\sqrt{H^3\log(2HK^2/\delta)/t}$.
--
--   Differences from the source:
--   - reading: for all (x, a, h, k) … with probability at least 1 − δ → with probability at least 1 − δ, simultaneously for all h, k ∈ [K] and active balls B; reason: the proof takes a union bound to obtain the simultaneous event, which later lemmas use; the pointwise reading is weaker
--   - reading: Lemma C.3 in the AdaQL setting → Assumption 1 is a hypothesis; reason: AdaQL is analysed under Assumption 1 (p.10)
--   - generalization: δ the algorithm's confidence parameter → any δ ∈ (0, 1), independent of the algorithm's δ; reason: the source's case is δ = prm.δ
--   - generalization: AdaMB/AdaQL run with a given sequence of starting states {X_1^k}, action ã(B_h^k) (or a distribution on the ball), argmax with ties, rewards and transitions drawn from R_h and T_h → IsRun: starting states arbitrary random variables, action law any kernel supported on the ball's action cell, any argmax rule, only the conditional marginals of R_h^k and X_{h+1}^k fixed; reason: each choice of the source is a special case (reading R8); the statement holds for every such run
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma C.3, p.41

import Mathlib
import Definitions.Def_AdaDiscRL_adaQL
import Definitions.Def_AdaDiscRL_IsRun
import Definitions.Def_AdaDiscRL_Assumption1
import Definitions.Def_AdaDiscRL_encounters
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma C.3 (Concentration of Transition for AdaQL)** (arXiv:2110.15843v3, p.41). Under
Assumption 1, for a run of AdaQL, every `δ ∈ (0, 1)` and every deterministic weight family
`(α_t^i)`, with probability at least `1 − δ`, simultaneously for all `(h, k)`, active `B ∈ P_h^k`
(`t`, `k_i` as in Lemma C.1):
`|Σ_{i=1}^t α_t^i (V⋆_{h+1}(X_{h+1}^{k_i}) − 𝔼_{Y∼T_h(·|X_h^{k_i},A_h^{k_i})}[V⋆_{h+1}(Y)])| ≤
H √(2 Σ_{i=1}^t (α_t^i)² log(2HK²/δ))`.
Moreover, for the weights of Eq. (11) the right-hand side is at most
`Tucb = 2√(H³ log(2HK²/δ)/t)` (`t ≥ 1`).

**Formalization Note.** Simultaneous event, as in C.1. `V⋆_{H+1} ≡ 0`. Assumption 1 (the setting of
AdaQL, p.10) makes `V⋆` continuous, so the expectations are genuine. -/
theorem lemma_C_3 {S A ι : Type} [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S]
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
    (h1 : Assumption1 M D prm.LV)
    (hrun : IsRun M P choose play (statesQL P prm choose) prm.K μ traj)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1) (w : ℕ → ℕ → ℝ) :
    1 - δ ≤ (μ {ω | ∀ k ∈ Finset.Icc 1 prm.K, ∀ h : Fin H, ∀ B,
      isActive P (statesQL P prm choose (traj ω) k h) B →
      |∑ i : Fin (encounters P choose (statesQL P prm choose) (traj ω) k h B).card, w (encounters P choose (statesQL P prm choose) (traj ω) k h B).card (i.val + 1) *
          (optVRem M (H - 1 - h.val) ((traj ω (encEp P choose (statesQL P prm choose) (traj ω) k h B i)).1 h.succ) -
            ∫ y, optVRem M (H - 1 - h.val) y ∂(M.T h ((traj ω (encEp P choose (statesQL P prm choose) (traj ω) k h B i)).1 h.castSucc, (traj ω (encEp P choose (statesQL P prm choose) (traj ω) k h B i)).2.1 h)))| ≤
        (H : ℝ) * Real.sqrt (2 * ∑ i : Fin (encounters P choose (statesQL P prm choose) (traj ω) k h B).card, (w (encounters P choose (statesQL P prm choose) (traj ω) k h B).card (i.val + 1)) ^ 2 * Real.log (2 * H * (prm.K : ℝ) ^ 2 / δ))}).toReal ∧
    ∀ t : ℕ, 1 ≤ t →
      (H : ℝ) * Real.sqrt (2 * ∑ i ∈ Finset.Icc 1 t, (VLearning.CCE.lrW H t i) ^ 2 * Real.log (2 * H * (prm.K : ℝ) ^ 2 / δ)) ≤
        2 * Real.sqrt ((H : ℝ) ^ 3 * Real.log (2 * H * (prm.K : ℝ) ^ 2 / δ) / t) := by sorry

end AdaDiscRL
