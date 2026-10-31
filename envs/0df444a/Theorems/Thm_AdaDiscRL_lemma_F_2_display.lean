-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_F_2_display
-- name    : AdaDiscRL.lemma_F_2_display
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:24.160145+00:00
-- url     : https://prove2.me/theorems/98c0e893-b0fb-4bef-b5c0-78f4193cba58
-- title:
--   Proof of Lemma F.2, display (p.51) — weighted regret decomposition
-- statement:
--   There are absolute constants $c,a>0$ such that, with $C_L=aL$ and $L=1+L_r+L_V+L_VL_T$, for a run of AdaQL under Assumption 1, or of AdaMB (bonus constant $c$, $L_V>0$) under Assumptions 1 and 2, with probability at least $1-2\delta$,
--   $$
--   \mathrm{Regret}(K)\le\sum_{k=1}^K\sum_{h=1}^H\Big(1+\frac1H\Big)^{2(h-1)}\mathrm{clip}\Big[\mathbb 1[n^{k-1}_h(B^k_h)=0]\,H\,\mathbb 1[\mathrm{AdaQL}]+C_L\mathrm{diam}(B^k_h)+\mathrm{Conf}^{k-1}_h(B^k_h)\ \Big|\ \frac{\mathrm{gap}_h(B^k_h)}{H+1}\Big]+\sum_{k=1}^K\sum_{h=1}^H\Big(1+\frac1H\Big)^{2h}\xi^k_{h+1},
--   $$
--   where $\xi^k_{h+1}=\mathbb E_{Y\sim T_h(\cdot\mid X^k_h,A^k_h)}[W(Y)]-W(X^k_{h+1})$ with $W=V^\star_{h+1}-V^{\pi^k}_{h+1}$ (AdaQL) or $W=\overline{\mathbf V}^{k-1}_{h+1}-V^{\pi^k}_{h+1}$ (AdaMB), and Conf is as in Lemma D.2.
--
--   This is the step of the regret analysis that separates the clipped per-ball confidence terms from a martingale term.
--
--   Differences from the source:
--   - encoding: outer sum Σ_{k=1}^H in the martingale term → Σ_{k=1}^K; reason: typo: the sum runs over episodes
--   - reading: Conf_h^k(B) in Lemmas D.2/E.3/F.2 → the proof's quantity (p.47): 2√(12 H³ log(2HK²/δ)/t) for AdaQL, 2 Rucb + 2 Tucb for AdaMB; reason: the §3.4 Conf does not dominate these bonuses (for d_S ≤ 2 Tucb has log K, Conf has √ι); the proof defines Conf this way (reading R5)
--   - reading: C_L a constant depending (linearly) on the Lipschitz constants → C_L = a L, L = 1 + L_r + L_V + L_V L_T, with a universal a > 0; reason: p.51: 'depending linearly with respect to the Lipschitz constant' (reading R2)
--   - reading: c an absolute constant in Tucb (p.17) → ∃ c > 0 quantified before all types, and the run uses prm.c = c; reason: the paper fixes c once (reading R4)
--   - generalization: initial estimates H − h + 1 (Algorithm 1, line 2) or H (Lemma 3.2, proof of D.1) → any v₀(h) ∈ [H − h + 1, H]; reason: covers both printed initializations (reading R7)
--   - encoding: gap_h(B) = min_{(x,a)∈B} gap_h(x, a) → the infimum ⨅ over the region; reason: the minimum need not be attained on a half-open region
--   - generalization: AdaMB/AdaQL run with a given sequence of starting states {X_1^k}, action ã(B_h^k) (or a distribution on the ball), argmax with ties, rewards and transitions drawn from R_h and T_h → IsRun: starting states arbitrary random variables, action law any kernel supported on the ball's action cell, any argmax rule, only the conditional marginals of R_h^k and X_{h+1}^k fixed; reason: each choice of the source is a special case (reading R8); the statement holds for every such run
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, proof of Lemma F.2, display, p.51 (ξ: pp.49–50)

import Mathlib
import Definitions.Def_AdaDiscRL_adaMB
import Definitions.Def_AdaDiscRL_encounters
import Definitions.Def_AdaDiscRL_IsRun
import Definitions.Def_AdaDiscRL_Assumption1
import Definitions.Def_AdaDiscRL_Assumption2
import Definitions.Def_AdaDiscRL_regret
import Definitions.Def_AdaDiscRL_clip
import Definitions.Def_AdaDiscRL_gap
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Proof of Lemma F.2, display** (arXiv:2110.15843v3, p.51): the weighted regret decomposition.
There are absolute constants `c, a > 0` such that, with `C_L = a L`, `L = 1 + L_r + L_V + L_V L_T`,
for a run of AdaQL under Assumption 1, or of AdaMB (constant `c`) under Assumptions 1 and 2 with
`L_V > 0`, with probability at least `1 − 2δ`,
`Regret(K) ≤ Σ_{k=1}^K Σ_{h=1}^H (1 + 1/H)^{2(h−1)} clip[1[n_h^{k−1}(B_h^k)=0] H 1[AdaQL] +
C_L diam(B_h^k) + Conf_h^{k−1}(B_h^k) | gap_h(B_h^k)/(H + 1)] + Σ_{k=1}^K Σ_{h=1}^H (1 + 1/H)^{2h} ξ_{h+1}^k`,
with `ξ_{h+1}^k = 𝔼_{T_h(·|X_h^k,A_h^k)}[W] − W(X_{h+1}^k)`, `W = V⋆_{h+1} − V^{π^k}_{h+1}` (AdaQL,
p.50) or `W = V̄^{k−1}_{h+1} − V^{π^k}_{h+1}` (AdaMB, p.50).

**Formalization Note.** The last outer sum is printed `Σ_{k=1}^H`; it is `Σ_{k=1}^K`. `Conf` is the
quantity of Lemma D.2's proof (R5). Steps are 0-based (`h : Fin H` is step `h + 1`). -/
theorem lemma_F_2_display : ∃ c a : ℝ, 0 < c ∧ 0 < a ∧
    ∀ {S A ι : Type} [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S]
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
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (traj : Ω → ℕ → EpData S A H),
    (Assumption1 M D prm.LV →
      IsRun M P choose play (statesQL P prm choose) prm.K μ traj →
      1 - 2 * prm.δ ≤ (μ {ω |
        regret M P choose play (statesQL P prm choose) prm.K (traj ω) ≤
          ∑ k ∈ Finset.Icc 1 prm.K, ∑ h : Fin H,
            (1 + 1 / (H : ℝ)) ^ (2 * h.val) *
              clip ((if (statesQL P prm choose (traj ω) (k - 1) h).n (selAt P choose (statesQL P prm choose) (traj ω) k h) = 0 then (H : ℝ) else 0) + a * (1 + prm.Lr + prm.LV + prm.LV * prm.LT) * P.diam (selAt P choose (statesQL P prm choose) (traj ω) k h) + 2 * Real.sqrt (12 * (H : ℝ) ^ 3 * prm.iota / ((statesQL P prm choose (traj ω) (k - 1) h).n (selAt P choose (statesQL P prm choose) (traj ω) k h) : ℝ))) ((⨅ q : ↥(P.region (selAt P choose (statesQL P prm choose) (traj ω) k h)), gap M h q) / ((H : ℝ) + 1)) +
          ∑ k ∈ Finset.Icc 1 prm.K, ∑ h : Fin H, (1 + 1 / (H : ℝ)) ^ (2 * (h.val + 1)) * ((∫ y, (optVRem M (H - 1 - h.val) y - polVRem M (greedyPolicy P choose play (statesQL P prm choose (traj ω) (k - 1))) (H - 1 - h.val) y) ∂(M.T h ((traj ω k).1 h.castSucc, (traj ω k).2.1 h))) -
              (optVRem M (H - 1 - h.val) ((traj ω k).1 h.succ) - polVRem M (greedyPolicy P choose play (statesQL P prm choose (traj ω) (k - 1))) (H - 1 - h.val) ((traj ω k).1 h.succ)))}).toReal) ∧
    (prm.c = c → 0 < prm.LV → Assumption1 M D prm.LV → Assumption2 M D prm.Lr prm.LT →
      IsRun M P choose play (statesMB P prm choose) prm.K μ traj →
      1 - 2 * prm.δ ≤ (μ {ω |
        regret M P choose play (statesMB P prm choose) prm.K (traj ω) ≤
          ∑ k ∈ Finset.Icc 1 prm.K, ∑ h : Fin H,
            (1 + 1 / (H : ℝ)) ^ (2 * h.val) *
              clip (0 + a * (1 + prm.Lr + prm.LV + prm.LV * prm.LT) * P.diam (selAt P choose (statesMB P prm choose) (traj ω) k h) + (2 * prm.rucbMB ((statesMB P prm choose (traj ω) (k - 1) h).n (selAt P choose (statesMB P prm choose) (traj ω) k h)) + 2 * prm.tucbMB ((statesMB P prm choose (traj ω) (k - 1) h).n (selAt P choose (statesMB P prm choose) (traj ω) k h)))) ((⨅ q : ↥(P.region (selAt P choose (statesMB P prm choose) (traj ω) k h)), gap M h q) / ((H : ℝ) + 1)) +
          ∑ k ∈ Finset.Icc 1 prm.K, ∑ h : Fin H, (1 + 1 / (H : ℝ)) ^ (2 * (h.val + 1)) * ((∫ y, ((fun y => if hh : h.val + 1 < H then VbarMB P prm ((statesMB P prm choose (traj ω) (k - 1)) ⟨h.val + 1, hh⟩) y else 0) y - polVRem M (greedyPolicy P choose play (statesMB P prm choose (traj ω) (k - 1))) (H - 1 - h.val) y) ∂(M.T h ((traj ω k).1 h.castSucc, (traj ω k).2.1 h))) -
              ((fun y => if hh : h.val + 1 < H then VbarMB P prm ((statesMB P prm choose (traj ω) (k - 1)) ⟨h.val + 1, hh⟩) y else 0) ((traj ω k).1 h.succ) - polVRem M (greedyPolicy P choose play (statesMB P prm choose (traj ω) (k - 1))) (H - 1 - h.val) ((traj ω k).1 h.succ)))}).toReal) := by sorry

end AdaDiscRL
