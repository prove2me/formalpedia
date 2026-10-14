-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_theorem4_1_supervised_regret
-- name    : CorruptRobustRL.Supervised.theorem4_1_supervised_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:27.937457+00:00
-- url     : https://prove2.me/theorems/796f3828-8411-40f5-afe2-8231998882a8
-- title:
--   Theorem 4.1, p. 17 — Regret $\le CH+8eH^2\sum_{\ell>\ell_\star}\ell q_\ell\sum_k\Delta_{k,\ell}+8eCH^2\log_2(2C)q_{\le\ell_\star}\sum_k\Delta_{k,\le\ell_\star}$
-- statement:
--   Consider SuperVIsed.C on a tabular nominal MDP (finite states, finite nonempty actions, stage-independent transitions, mean rewards in $[0,1]$) with horizon $H\ge1$, $\ell_{\max}\ge1$ base learners and $K$ episodes, and let $C$ be an integer with $1\le C\le2^{\ell_{\max}}$ (the number of corrupted episodes). In episode $k$ the learners run UCBVI-BASE with nested active sets, global estimates $(\hat r_{k,\mathrm{gl}},\hat p_{k,\mathrm{gl}})$, global bonuses $b_{k,\mathrm{gl},\ell}$ and subsampled model-estimates $(\hat r_{k,\mathrm{sb},\ell},\hat p_{k,\mathrm{sb},\ell},b_{k,\mathrm{sb},\ell})$, all with the tabular ranges, and with any argmax selector; $\mathcal T_{k,\ell}$ is the Q-supervisor of learner $\ell$ and $\pi^{\mathrm{master}}_k$ the master policy.
--
--   Let $\ell_\star=\min\{\ell\ge1:2^\ell\ge C\}$, $\mathcal V_{k,\ell,h+1}=\{\bar V_{k,\ell,h+1}-V^\star_{h+1},\ \bar V_{k,\ell,h+1}-\underline V_{k,\ell,h+1}\}$ and
--   $$\Delta_{k,\ell}=E^{\pi^{\mathrm{master}}_{k,\ell}}\Big[\sum_{h=1}^H\Big(\min\Big(3H,\,2b_{k,\mathrm{sb},\ell}(x_h,a_h)+\max_{V\in\mathcal V_{k,\ell;h+1}}(\hat p_{k,\mathrm{sb},\ell}(x_h,a_h)-p^\star(x_h,a_h))^\top V\Big)\Big)_+\Big],$$
--   $$\Delta_{k,\le\ell_\star}=E^{\pi^{\mathrm{master}}_{k,\le\ell_\star}}\Big[\sum_{h=1}^H\Big(\min\Big(3H,\,2b_{k,\mathrm{gl},\ell_\star}(x_h,a_h)+\max_{V\in\mathcal V_{k,\ell_\star;h+1}}(\hat p_{k,\mathrm{gl}}(x_h,a_h)-p^\star(x_h,a_h))^\top V\Big)\Big)_+\Big].$$
--   If the global and subsampled model-estimates of every learner $\ell\ge\ell_\star$ are valid with respect to $\mathcal T_{k,\ell}$ in every episode $k$, then
--   $$CH+\sum_{k=1}^K\big(V^\star-V^{\pi^{\mathrm{master}}_k}\big)\le CH+8eH^2\sum_{\ell_\star<\ell\le\ell_{\max}}\ell\,q_\ell\sum_k\Delta_{k,\ell}+8eCH^2\log_2(2C)\,q_{\le\ell_\star}\sum_k\Delta_{k,\le\ell_\star}.$$
--
--   The left side is the paper's upper bound (2.2) on the regret. The theorem bounds it by the expected bonuses of the critically tolerant learner $\ell_\star$ and of the robust learners $\ell>\ell_\star$; Theorems 2.1 and 2.2 follow by bounding these bonus sums with concentration arguments.
--
--   **Formalization Note** Four departures from the printed statement. (1) The constant of the first term is $8eH^2$, as the proof on p. 20 produces ($2H$ from Proposition 4.2 with $1+H\le2H$, times $\rho_{k,\ell}\le4eH\ell$ from Lemma 4.10); the page prints $4eH^2$, and the second term's $8eCH^2\log(2C)=2H\cdot4eCH\log(2C)$ is consistent with $8eH^2$. (2) Each summand of $\Delta$ carries a positive part $(\cdot)_+$: the bound of Lemma 4.7 can be negative, and the proof passes through Proposition 4.2, which needs a nonnegative integrand. (3) The setting is tabular with mean rewards, and the regret is the upper bound (2.2), which the paper itself uses from p. 7 on. (4) The base policy maximizes the upper estimate over the active set (Algorithm 2), for every argmax selector, and an empty filtered active set is replaced by the learner's own (a convention that never fires for learners $\ell\ge\ell_\star$ under the hypotheses). The logarithm is base 2. The page's $\bar V_{k;h+1}$ in $\mathcal V$ is read as $\bar V_{k,\ell,h+1}$, and the stray "cdot" as a product. $\ell_{\max}$ is a free parameter with $C\le2^{\ell_{\max}}$, which holds for the paper's $\ell_{\max}=\lceil\log T\rceil$ because $C\le K\le T$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 17, Theorem 4.1; proof pp. 17–20; regret upper bound (2.2), p. 7

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

namespace CorruptRobustRL.Supervised

open Finset QSupervisor

/-- Theorem 4.1 (p. 17), tabular, with the regret upper bound (2.2), the constant `8eH²` of the
proof (p. 20) and positive parts in `Δ`: if for every episode `k` the global and subsampled
model-estimates of every learner `ℓ ≥ ℓ⋆` are valid, then
`CH + Σ_k (V⋆ − V^{π^master_k}) ≤ CH + 8eH² Σ_{ℓ>ℓ⋆} ℓ q_ℓ Σ_k Δ_{k,ℓ} + 8eCH² log₂(2C) q_{≤ℓ⋆} Σ_k Δ_{k,≤ℓ⋆}`. -/
theorem theorem4_1_supervised_regret
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal)
    (H ℓmax K C : ℕ) (hH : 1 ≤ H) (hℓmax : 1 ≤ ℓmax) (hC : 1 ≤ C) (hCℓ : C ≤ 2 ^ ℓmax)
    (E : Fin K → EpisodeEst X A)
    (hrange : ∀ k ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax →
      ((E k).gl ℓ).IsModelEst H ∧ ((E k).sb ℓ).IsModelEst H)
    (sel : Selector A) (hsel : IsArgmaxSelector sel)
    (hvalid : ∀ k ℓ, lstar C ≤ ℓ → ℓ ≤ ℓmax →
      ((E k).gl ℓ).IsValid M H (layerSup H ℓmax (E k) sel ℓ) ∧
        ((E k).sb ℓ).IsValid M H (layerSup H ℓmax (E k) sel ℓ)) :
    (C : ℝ) * H + ∑ k, (Vstar0 M H - mixValue M H (master H ℓmax (basePolicies H ℓmax (E k) sel))) ≤
      (C : ℝ) * H
        + 8 * Real.exp 1 * (H : ℝ) ^ 2 *
            (∑ ℓ ∈ Ioc (lstar C) ℓmax, (ℓ : ℝ) * q H ℓmax ℓ * ∑ k, deltaEq M H ℓmax (E k) sel ℓ)
        + 8 * Real.exp 1 * (C : ℝ) * (H : ℝ) ^ 2 * Real.logb 2 (2 * C) * qLe H ℓmax (lstar C) *
            ∑ k, deltaLe M H ℓmax (E k) sel (lstar C) := by sorry

end CorruptRobustRL.Supervised
