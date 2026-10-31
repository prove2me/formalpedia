-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_E_3
-- name    : AdaDiscRL.lemma_E_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:58.310041+00:00
-- url     : https://prove2.me/theorems/066f2c7b-90fb-4d6c-a02a-affbf296a8e7
-- title:
--   Lemma E.3 — one-step clipped bound (corrected: first-visit term for AdaMB; $\mathcal D_{\mathcal S}\le\mathcal D$)
-- statement:
--   There are absolute constants $c,C_L>0$ such that, for a run of AdaQL under Assumption 1, or of AdaMB (bonus constant $c$, $L_V>0$, $\mathcal D_{\mathcal S}(x,x')\le\mathcal D((x,a),(x',a))$) under Assumptions 1 and 2, with probability at least $1-2\delta$, for all $k\in[K]$ and steps $h$, with $t=n^{k-1}_h(B^k_h)$,
--   $$
--   \overline{\mathbf V}^{k-1}_h(X^k_h)-Q^\star_h(X^k_h,A^k_h)\le\mathrm{clip}\Big[\mathbb 1[t=0]v_0(h)+C_L\mathrm{Bias}(B^k_h)+\mathrm{Conf}^{k-1}_h(B^k_h)\ \Big|\ \frac{\mathrm{gap}_h(B^k_h)}{H+1}\Big]+\Big(1+\frac1H\Big)f^{k-1}_{h+1},
--   $$
--   where $\mathrm{gap}_h(B)=\inf_{(x,a)\in B}\mathrm{gap}_h(x,a)$, $f^{k-1}_{h+1}=\sum_{i=1}^t\alpha^i_t(\overline{\mathbf V}^{k_i-1}_{h+1}-V^\star_{h+1})(X^{k_i}_{h+1})$ for AdaQL ($k_i$ the encounters of $B^k_h$ before episode $k$) and $f^{k-1}_{h+1}=\mathbb E_{T_h(\cdot\mid X^k_h,A^k_h)}[\overline{\mathbf V}^{k-1}_{h+1}]-\mathbb E_{T_h(\cdot\mid X^k_h,A^k_h)}[V^\star_{h+1}]$ for AdaMB, and Conf is as in Lemma D.2.
--
--   Differences from the source:
--   - correction: first-visit term 1[t=0] H 1[AdaQL] → 1[t=0] v₀(h) for both algorithms; reason: for AdaMB at k = 1 with H = 1, r ≡ 0, L_r = L_V = L_T = 0 the printed bound reads v₀ ≤ 0; with the term the bound holds since v₀(h) ≥ gap/(H+1) and f ≥ 0
--   - correction: Lemma E.3 for AdaMB with any metric D ≤ D_S + D_A → AdaMB part assumes D_S(x, x′) ≤ D((x, a), (x′, a)); reason: counterexample: S = [0, s], A a point, D = D_S/s (an admissible metric with diameter 1), T ≡ δ₀, r ≡ 0; V̄ and T̄ use D_S-distances to cell centers that are (s/2)·diam(B), which breaks the bound for large s
--   - reading: Conf_h^k(B) in Lemmas D.2/E.3/F.2 → the proof's quantity (p.47): 2√(12 H³ log(2HK²/δ)/t) for AdaQL, 2 Rucb + 2 Tucb for AdaMB; reason: the §3.4 Conf does not dominate these bonuses (for d_S ≤ 2 Tucb has log K, Conf has √ι); the proof defines Conf this way (reading R5)
--   - correction: V̄_{h+1}^{k_i}(X_{h+1}^{k_i}) → V̄_{h+1}^{k_i − 1}(X_{h+1}^{k_i}); reason: the update rule Eq. (9) uses V̄^{k−1}_{h+1}; the two differ on any run where step h+1's estimates change in episode k_i (correction C9)
--   - generalization: initial estimates H − h + 1 (Algorithm 1, line 2) or H (Lemma 3.2, proof of D.1) → any v₀(h) ∈ [H − h + 1, H]; reason: covers both printed initializations (reading R7)
--   - reading: C_L a constant depending on the Lipschitz constants → a universal constant C_L > 0 multiplying Bias (which already carries L_r, L_V, L_T), quantified before all types; reason: the proof's constants are absolute multiples of Bias (8 for AdaQL, at most 3/2 for AdaMB)
--   - reading: c an absolute constant in Tucb (p.17) → ∃ c > 0 quantified before all types, and the run uses prm.c = c; reason: the paper fixes c once (reading R4)
--   - encoding: gap_h(B) = min_{(x,a)∈B} gap_h(x, a) → the infimum ⨅ over the region; reason: the minimum need not be attained on a half-open region
--   - generalization: AdaMB/AdaQL run with a given sequence of starting states {X_1^k}, action ã(B_h^k) (or a distribution on the ball), argmax with ties, rewards and transitions drawn from R_h and T_h → IsRun: starting states arbitrary random variables, action law any kernel supported on the ball's action cell, any argmax rule, only the conditional marginals of R_h^k and X_{h+1}^k fixed; reason: each choice of the source is a special case (reading R8); the statement holds for every such run
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma E.3, p.49

import Mathlib
import Definitions.Def_AdaDiscRL_adaMB
import Definitions.Def_AdaDiscRL_gap
import Definitions.Def_AdaDiscRL_IsRun
import Definitions.Def_AdaDiscRL_Assumption1
import Definitions.Def_AdaDiscRL_Assumption2
import Definitions.Def_AdaDiscRL_encounters
import Definitions.Def_AdaDiscRL_clip
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma E.3** (arXiv:2110.15843v3, p.49), with the confidence term of Lemma D.2's proof and two
corrections. There are absolute constants `c, C_L > 0` such that, for a run of AdaQL under
Assumption 1, or of AdaMB (constant `c`) under Assumptions 1 and 2 with `L_V > 0`, with probability
at least `1 − 2δ`, for all `(h, k) ∈ [H] × [K]`, with `t = n_h^{k−1}(B_h^k)`:
`V̄_h^{k−1}(X_h^k) − Q⋆_h(X_h^k, A_h^k) ≤ clip[1[t=0] v₀(h) + C_L Bias(B_h^k) + Conf_h^{k−1}(B_h^k) |
gap_h(B_h^k)/(H + 1)] + (1 + 1/H) f_{h+1}^{k−1}`, where `gap_h(B) = inf_{(x,a)∈B} gap_h(x, a)`,
`f = Σ_i α_t^i (V̄_{h+1}^{k_i−1} − V⋆_{h+1})(X_{h+1}^{k_i})` (AdaQL, `k_i` the encounters of `B_h^k`
before episode `k`) and `f = 𝔼_{T_h(·|X_h^k,A_h^k)}[V̄_{h+1}^{k−1}] − 𝔼_{T_h(·|X_h^k,A_h^k)}[V⋆_{h+1}]`
(AdaMB).

**Formalization Note.** `Conf` as in Lemma D.2 (R5). Corrections: (i) the first-visit term
`1[t=0] H 1[AdaQL]` is `1[t=0] v₀(h)` for both algorithms: for AdaMB at `k = 1`, `H = 1`,
`r ≡ 0`, `L_r = L_V = L_T = 0`, the printed bound reads `v₀ ≤ 0`. (ii) For AdaMB,
`D_S(x, x′) ≤ D((x, a), (x′, a))` is assumed, as in Lemma D.2 (with `S = [0, s]`, `D = D_S/s`,
`s > 4 C_L`, `k = 1`, the left side exceeds the right). -/
theorem lemma_E_3 : ∃ c CL : ℝ, 0 < c ∧ 0 < CL ∧
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
      1 - 2 * prm.δ ≤ (μ {ω | ∀ k ∈ Finset.Icc 1 prm.K, ∀ h : Fin H,
        VbarQL P (statesQL P prm choose (traj ω) (k - 1)) h ((traj ω k).1 h.castSucc) - optQ M h ((traj ω k).1 h.castSucc, (traj ω k).2.1 h) ≤
          clip ((if (encounters P choose (statesQL P prm choose) (traj ω) (k - 1) h (selAt P choose (statesQL P prm choose) (traj ω) k h)).card = 0 then prm.v0 h else 0) +
              CL * prm.biasQL (P.diam (selAt P choose (statesQL P prm choose) (traj ω) k h)) + 2 * Real.sqrt (12 * (H : ℝ) ^ 3 * prm.iota / ((encounters P choose (statesQL P prm choose) (traj ω) (k - 1) h (selAt P choose (statesQL P prm choose) (traj ω) k h)).card : ℝ)))
            ((⨅ q : ↥(P.region (selAt P choose (statesQL P prm choose) (traj ω) k h)), gap M h q) / ((H : ℝ) + 1)) +
          (1 + 1 / (H : ℝ)) * (∑ i : Fin (encounters P choose (statesQL P prm choose) (traj ω) (k - 1) h (selAt P choose (statesQL P prm choose) (traj ω) k h)).card, VLearning.CCE.lrW H (encounters P choose (statesQL P prm choose) (traj ω) (k - 1) h (selAt P choose (statesQL P prm choose) (traj ω) k h)).card (i.val + 1) *
              (VnextQL P (statesQL P prm choose (traj ω) (encEp P choose (statesQL P prm choose) (traj ω) (k - 1) h (selAt P choose (statesQL P prm choose) (traj ω) k h) i - 1)) h ((traj ω (encEp P choose (statesQL P prm choose) (traj ω) (k - 1) h (selAt P choose (statesQL P prm choose) (traj ω) k h) i)).1 h.succ) -
                optVRem M (H - 1 - h.val) ((traj ω (encEp P choose (statesQL P prm choose) (traj ω) (k - 1) h (selAt P choose (statesQL P prm choose) (traj ω) k h) i)).1 h.succ)))}).toReal) ∧
    (prm.c = c → 0 < prm.LV → Assumption1 M D prm.LV → Assumption2 M D prm.Lr prm.LT →
      (∀ (x x' : S) (a : A), dist x x' ≤ D (x, a) (x', a)) →
      IsRun M P choose play (statesMB P prm choose) prm.K μ traj →
      1 - 2 * prm.δ ≤ (μ {ω | ∀ k ∈ Finset.Icc 1 prm.K, ∀ h : Fin H,
        VbarMB P prm (statesMB P prm choose (traj ω) (k - 1) h) ((traj ω k).1 h.castSucc) - optQ M h ((traj ω k).1 h.castSucc, (traj ω k).2.1 h) ≤
          clip ((if (statesMB P prm choose (traj ω) (k - 1) h).n (selAt P choose (statesMB P prm choose) (traj ω) k h) = 0 then prm.v0 h else 0) +
              CL * prm.biasMB (P.diam (selAt P choose (statesMB P prm choose) (traj ω) k h)) + 2 * prm.rucbMB ((statesMB P prm choose (traj ω) (k - 1) h).n (selAt P choose (statesMB P prm choose) (traj ω) k h)) + 2 * prm.tucbMB ((statesMB P prm choose (traj ω) (k - 1) h).n (selAt P choose (statesMB P prm choose) (traj ω) k h)))
            ((⨅ q : ↥(P.region (selAt P choose (statesMB P prm choose) (traj ω) k h)), gap M h q) / ((H : ℝ) + 1)) +
          (1 + 1 / (H : ℝ)) * ((if hh : h.val + 1 < H then ∫ y, VbarMB P prm ((statesMB P prm choose (traj ω) (k - 1)) ⟨h.val + 1, hh⟩) y ∂(M.T h ((traj ω k).1 h.castSucc, (traj ω k).2.1 h)) else 0) - ∫ y, optVRem M (H - 1 - h.val) y ∂(M.T h ((traj ω k).1 h.castSucc, (traj ω k).2.1 h)))}).toReal) := by sorry

end AdaDiscRL
