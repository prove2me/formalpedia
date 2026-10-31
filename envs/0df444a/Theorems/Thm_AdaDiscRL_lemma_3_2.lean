-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_3_2
-- name    : AdaDiscRL.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:14.342199+00:00
-- url     : https://prove2.me/theorems/b67a2b85-2109-4884-8d47-17404a7cbc7b
-- title:
--   Lemma 3.2 — the unrolled AdaQL estimate (corrected: $\overline{\mathbf V}^{k_i-1}_{h+1}$)
-- statement:
--   Consider AdaQL on any data sequence. Fix an episode $k\in[K]$, a step $h$ and an active ball $B\in\mathcal P^k_h$, and let $k_1<\dots<k_t\le k$ be the episodes at which $B$ or one of its ancestors was selected at step $h$. Then $t=n^k_h(B)$ and
--   $$
--   \overline{\mathbf Q}^k_h(B)=\mathbb 1[t=0]\,v_0(h)+\sum_{i=1}^t\alpha^i_t\Big(R^{k_i}_h+\mathrm{Rucb}^{k_i}_h(B^{k_i}_h)+\overline{\mathbf V}^{k_i-1}_{h+1}(X^{k_i}_{h+1})+\mathrm{Tucb}^{k_i}_h(B^{k_i}_h)+\mathrm{Bias}(B^{k_i}_h)\Big),
--   $$
--   where $\alpha^i_t$ are the weights of Eq. (11), $B^{k_i}_h$ the selected balls and $\overline{\mathbf V}_{H+1}\equiv0$.
--
--   The identity rewrites the recursive update (9) as a weighted average over all past encounters of the ball's ancestry; Lemmas D.1–D.2 subtract $Q^\star_h$ from it term by term.
--
--   Differences from the source:
--   - correction: V̄_{h+1}^{k_i}(X_{h+1}^{k_i}) → V̄_{h+1}^{k_i − 1}(X_{h+1}^{k_i}); reason: the update rule Eq. (9) uses V̄^{k−1}_{h+1}; the two differ on any run where step h+1's estimates change in episode k_i (correction C9)
--   - generalization: initial estimates H − h + 1 (Algorithm 1, line 2) or H (Lemma 3.2, proof of D.1) → any v₀(h) ∈ [H − h + 1, H]; reason: covers both printed initializations (reading R7)
--   - reading: t = n_h^k(B), the number of times B or its ancestors were encountered → t is the number of encounter episodes, and t = n_h^k(B) is a conclusion; reason: the paper identifies the count with the number of encounters (p.16); Lean states the identification
--   - generalization: invariants of the algorithm's run → stated for every data sequence (pathwise); reason: the claim is deterministic; a run's data sequence is one data sequence
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma 3.2, p.18

import Mathlib
import Definitions.Def_AdaDiscRL_adaQL
import Definitions.Def_AdaDiscRL_encounters
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma 3.2 (Recursive Relationship for AdaQL)** (arXiv:2110.15843v3, p.18), corrected. For
`k ∈ [K]`, a step `h` and an active ball `B ∈ P_h^k` of AdaQL, let `k₁ < ⋯ < k_t ≤ k` be the
episodes at which `B` or one of its ancestors was selected at step `h`. Then `t = n_h^k(B)` and
`Q̄_h^k(B) = 1[t=0] v₀(h) + Σ_{i=1}^t α_t^i (R_h^{k_i} + Rucb_h^{k_i}(B_h^{k_i}) +
V̄_{h+1}^{k_i−1}(X_{h+1}^{k_i}) + Tucb_h^{k_i}(B_h^{k_i}) + Bias(B_h^{k_i}))`.

**Formalization Note.** Pathwise: for every data sequence. The printed `V̄_{h+1}^{k_i}` is replaced by
`V̄_{h+1}^{k_i−1}`, the value the update rule Eq. (9) uses; the printed `H` by the initial value
`v₀(h)`. Step `h : Fin H` is the paper's `h + 1`; `V̄_{H+1} ≡ 0`. -/
theorem lemma_3_2 {S A ι : Type} [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S]
    [BorelSpace S] [MetricSpace A] [CompactSpace A] [Nonempty A] [MeasurableSpace A]
    [BorelSpace A]
    (D : S × A → S × A → ℝ) {H : ℕ} (prm : AdaParams H)
    (P : HierPartition S A ι D prm.dS prm.K) (choose : Finset ι → (ι → ℝ) → ι)
    (hD : IsAdmissibleMetric D) (hH : 1 ≤ H) (hK : 1 ≤ prm.K) (hδ0 : 0 < prm.δ) (hδ1 : prm.δ < 1)
    (hLr : 0 ≤ prm.Lr) (hLV : 0 ≤ prm.LV) (hLT : 0 ≤ prm.LT)
    (hv0 : ∀ h : Fin H, (H : ℝ) - h ≤ prm.v0 h ∧ prm.v0 h ≤ H)
    (hchoose : IsArgmaxRule choose)
    (data : ℕ → EpData S A H) (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ prm.K) (h : Fin H) (B : ι)
    (hB : isActive P (statesQL P prm choose data k h) B) :
    (encounters P choose (statesQL P prm choose) data k h B).card =
        (statesQL P prm choose data k h).n B ∧
    (statesQL P prm choose data k h).Q B =
      (if (encounters P choose (statesQL P prm choose) data k h B).card = 0 then prm.v0 h else 0) +
      ∑ i : Fin (encounters P choose (statesQL P prm choose) data k h B).card,
        VLearning.CCE.lrW H (encounters P choose (statesQL P prm choose) data k h B).card (i.val + 1) *
          ((data (encEp P choose (statesQL P prm choose) data k h B i)).2.2 h +
           prm.rucbQL ((statesQL P prm choose data (encEp P choose (statesQL P prm choose) data k h B i) h).n
              (selAt P choose (statesQL P prm choose) data (encEp P choose (statesQL P prm choose) data k h B i) h)) +
           VnextQL P (statesQL P prm choose data (encEp P choose (statesQL P prm choose) data k h B i - 1)) h
              ((data (encEp P choose (statesQL P prm choose) data k h B i)).1 h.succ) +
           prm.tucbQL ((statesQL P prm choose data (encEp P choose (statesQL P prm choose) data k h B i) h).n
              (selAt P choose (statesQL P prm choose) data (encEp P choose (statesQL P prm choose) data k h B i) h)) +
           prm.biasQL (P.diam
              (selAt P choose (statesQL P prm choose) data (encEp P choose (statesQL P prm choose) data k h B i) h))) := by sorry

end AdaDiscRL
