-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_D_2
-- name    : AdaDiscRL.lemma_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:41.689147+00:00
-- url     : https://prove2.me/theorems/52c85a40-bcab-48b7-a718-ab2f2c0c4a8f
-- title:
--   Lemma D.2 — optimism of the estimates (corrected: $\mathcal D_{\mathcal S}\le\mathcal D$ for AdaMB's upper bound and last claim)
-- statement:
--   There are absolute constants $c,C_L>0$ such that, for a run of AdaQL under Assumption 1, or of AdaMB (bonus constant $c$, $L_V>0$) under Assumptions 1 and 2, with probability at least $1-2\delta$, simultaneously for all $k\in[K]$, steps $h$, active balls $B\in\mathcal P^k_h$ with $t=n^k_h(B)$ and $(x,a)\in B$:
--   $$
--   0\le\overline{\mathbf Q}^k_h(B)-Q^\star_h(x,a)\le\mathrm{Conf}^k_h(B)+C_L\,\mathrm{Bias}(B)+f^k_{h+1},\qquad 0\le\overline{\mathbf V}^k_h(x)-V^\star_h(x),
--   $$
--   (for AdaMB, the upper bound on $\overline{\mathbf Q}^k_h(B)-Q^\star_h(x,a)$ is asserted when $\mathcal D_{\mathcal S}(x,x')\le\mathcal D((x,a),(x',a))$),
--   and for AdaMB $0\le\widetilde{\mathbf V}^k_h(A)-V^\star_h(x)$ for every cell $A\in\mathcal S(\mathcal P^k_h)$ containing $x$, where
--   $$
--   f^k_{h+1}=\mathbb 1[t=0]v_0(h)+\sum_{i=1}^t\alpha^i_t\big(\overline{\mathbf V}^{k_i-1}_{h+1}-V^\star_{h+1}\big)(X^{k_i}_{h+1})\ \ (\text{AdaQL}),\qquad f^k_{h+1}=\mathbb E_{T_h(\cdot\mid x,a)}\big[\overline{\mathbf V}^k_{h+1}\big]-\mathbb E_{T_h(\cdot\mid x,a)}\big[V^\star_{h+1}\big]\ \ (\text{AdaMB}).
--   $$
--   In addition, $\overline{\mathbf V}^{k-1}_h(X^k_h)\le\overline{\mathbf Q}^{k-1}_h(B^k_h)+L_V\,\mathrm{diam}(B^k_h)$ (for AdaMB when $\mathcal D_{\mathcal S}(x,x')\le\mathcal D((x,a),(x',a))$). Here $\mathrm{Conf}=2\sqrt{12H^3\log(2HK^2/\delta)/t}$ (AdaQL) and $2\,\mathrm{Rucb}+2\,\mathrm{Tucb}$ (AdaMB).
--
--   Differences from the source:
--   - reading: Conf_h^k(B) in Lemmas D.2/E.3/F.2 → the proof's quantity (p.47): 2√(12 H³ log(2HK²/δ)/t) for AdaQL, 2 Rucb + 2 Tucb for AdaMB; reason: the §3.4 Conf does not dominate these bonuses (for d_S ≤ 2 Tucb has log K, Conf has √ι); the proof defines Conf this way (reading R5)
--   - reading: C_L Bias(B_h^k) → C_L Bias(B); reason: B_h^k is not defined for a general ball B at episode k; the proof (pp.46–47) bounds by Bias(B)
--   - correction: V̄_{h+1}^{k_i}(X_{h+1}^{k_i}) → V̄_{h+1}^{k_i − 1}(X_{h+1}^{k_i}); reason: the update rule Eq. (9) uses V̄^{k−1}_{h+1}; the two differ on any run where step h+1's estimates change in episode k_i (correction C9)
--   - generalization: initial estimates H − h + 1 (Algorithm 1, line 2) or H (Lemma 3.2, proof of D.1) → any v₀(h) ∈ [H − h + 1, H]; reason: covers both printed initializations (reading R7)
--   - reading: C_L a constant depending on the Lipschitz constants → a universal constant C_L > 0 multiplying Bias (which already carries L_r, L_V, L_T), quantified before all types; reason: the proof's constants are absolute multiples of Bias (8 for AdaQL, at most 3/2 for AdaMB)
--   - reading: c an absolute constant in Tucb (p.17) → ∃ c > 0 quantified before all types, and the run uses prm.c = c; reason: the paper fixes c once (reading R4)
--   - correction: Lemma D.2 (upper bound on Q̄ − Q⋆, and last claim) for AdaMB with any metric D ≤ D_S + D_A → these two AdaMB claims assume D_S(x, x′) ≤ D((x, a), (x′, a)); the lower bounds (optimism) do not; reason: counterexamples with S = [0, s], A a point, D = D_S/s (admissible, diameter 1). Last claim: k = 1, X_1^1 = s gives V̄^0(s) = v₀ + L_V s/2 > v₀ + L_V. Upper bound: H = 2, r ≡ 0, T ≡ δ₀, X_1^k = s; the never-selected step-1 ball [0, s/2) × A has T̄ uniform on the centers s/4, 3s/4, so Q̄_1 ≥ L_V s/32, while the right side is V̄_2(0) ≤ L_V s/64 + O(1) plus terms independent of s
--   - reading: 0 ≤ Ṽ_h^k(x) − V⋆_h(x) → 0 ≤ Ṽ_h^k(A) − V⋆_h(x) for every cell A ∈ S(P_h^k) and x ∈ A; reason: Ṽ is defined on cells (Eq. (7))
--   - reading: AdaMB setting → Assumptions 1 and 2 and L_V > 0 for AdaMB; Assumption 1 for AdaQL; reason: the paper's settings (p.10) and Lemma C.4
--   - generalization: AdaMB/AdaQL run with a given sequence of starting states {X_1^k}, action ã(B_h^k) (or a distribution on the ball), argmax with ties, rewards and transitions drawn from R_h and T_h → IsRun: starting states arbitrary random variables, action law any kernel supported on the ball's action cell, any argmax rule, only the conditional marginals of R_h^k and X_{h+1}^k fixed; reason: each choice of the source is a special case (reading R8); the statement holds for every such run
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma D.2, pp.43–44 (proof pp.44–47)

import Mathlib
import Definitions.Def_AdaDiscRL_adaMB
import Definitions.Def_AdaDiscRL_IsRun
import Definitions.Def_AdaDiscRL_Assumption1
import Definitions.Def_AdaDiscRL_Assumption2
import Definitions.Def_AdaDiscRL_encounters
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma D.2 (Optimism)** (arXiv:2110.15843v3, pp.43–44), with the confidence term of its proof
and one correction. There are absolute constants `c, C_L > 0` such that, for a run of AdaQL under
Assumption 1, or of AdaMB (constant `c`) under Assumptions 1 and 2 with `L_V > 0`, with probability
at least `1 − 2δ`, simultaneously for all `(h, k) ∈ [H] × [K]`, active `B ∈ P_h^k` with `t = n_h^k(B)`
and `(x, a) ∈ B`:
`0 ≤ Q̄_h^k(B) − Q⋆_h(x, a) ≤ Conf_h^k(B) + C_L Bias(B) + f_{h+1}^k` (for AdaMB, the upper bound
when `D_S(x, x′) ≤ D((x, a), (x′, a))`), `0 ≤ V̄_h^k(x) − V⋆_h(x)`, and
(AdaMB) `0 ≤ Ṽ_h^k(A) − V⋆_h(x)` for cells `A ∈ S(P_h^k)` containing `x`; with
`f = 1[t=0] v₀(h) + Σ_i α_t^i (V̄_{h+1}^{k_i−1} − V⋆_{h+1})(X_{h+1}^{k_i})` (AdaQL) and
`f = 𝔼_{T_h(·|x,a)}[V̄_{h+1}^k] − 𝔼_{T_h(·|x,a)}[V⋆_{h+1}]` (AdaMB). In addition
`V̄_h^{k−1}(X_h^k) ≤ Q̄_h^{k−1}(B_h^k) + L_V diam(B_h^k)`.

**Formalization Note.** `Conf` is the proof's quantity (p.47): `2√(12 H³ log(2HK²/δ)/t)` for AdaQL
and `2 Rucb + 2 Tucb` for AdaMB; `Bias(B_h^k)` is read `Bias(B)`; `V̄^{k_i}` is `V̄^{k_i−1}` (the value
used by Eq. (9)); `H` in `f` is `v₀(h)`. Correction: for AdaMB the upper bound on
`Q̄ − Q⋆` and the last claim assume `D_S(x, x′) ≤ D((x, a), (x′, a))`. Without it, the last claim
fails at `S = [0, 100]`, `A` a point, `D = D_S/100`, `k = 1`, `X_1^1 = 100`:
`V̄^0(100) = v₀ + 50 L_V > v₀ + L_V`. The upper bound fails at `S = [0, s]`, `A` a point,
`D = D_S/s`, `H = 2`, `r ≡ 0`, `T ≡ δ₀`, starting states `X_1^k = s` (so `Q⋆ ≡ 0`). The step-1
ball `B = [0, s/2) × A` is never selected. It keeps the root's count and has `T̄(·|B)` uniform on
the centers `s/4`, `3s/4`, so `Q̄_1(B) ≥ 𝔼_{T̄}[V̄_2] ≥ L_V s/32`. Step 2 is refined around `0`, and
once it reaches level 5 there, `V̄_2(0) ≤ L_V s/64 + O(1)`. The rest of the right side does not
depend on `s`, so the bound fails for large `s`. -/
theorem lemma_D_2 : ∃ c CL : ℝ, 0 < c ∧ 0 < CL ∧
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
        (∀ B, isActive P (statesQL P prm choose (traj ω) k h) B → ∀ p ∈ P.region B,
          0 ≤ (statesQL P prm choose (traj ω) k h).Q B - optQ M h p ∧
          (statesQL P prm choose (traj ω) k h).Q B - optQ M h p ≤
            2 * Real.sqrt (12 * (H : ℝ) ^ 3 * prm.iota / ((encounters P choose (statesQL P prm choose) (traj ω) k h B).card : ℝ)) + CL * prm.biasQL (P.diam B) + ((if (encounters P choose (statesQL P prm choose) (traj ω) k h B).card = 0 then prm.v0 h else 0) +
            ∑ i : Fin (encounters P choose (statesQL P prm choose) (traj ω) k h B).card, VLearning.CCE.lrW H (encounters P choose (statesQL P prm choose) (traj ω) k h B).card (i.val + 1) *
              (VnextQL P (statesQL P prm choose (traj ω) (encEp P choose (statesQL P prm choose) (traj ω) k h B i - 1)) h ((traj ω (encEp P choose (statesQL P prm choose) (traj ω) k h B i)).1 h.succ) -
                optVRem M (H - 1 - h.val) ((traj ω (encEp P choose (statesQL P prm choose) (traj ω) k h B i)).1 h.succ)))) ∧
        (∀ x, 0 ≤ VbarQL P (statesQL P prm choose (traj ω) k) h x - optV M h x) ∧
        VbarQL P (statesQL P prm choose (traj ω) (k - 1)) h ((traj ω k).1 h.castSucc) ≤
          (statesQL P prm choose (traj ω) (k - 1) h).Q (selAt P choose (statesQL P prm choose) (traj ω) k h) + prm.LV * P.diam (selAt P choose (statesQL P prm choose) (traj ω) k h)}).toReal) ∧
    (prm.c = c → 0 < prm.LV → Assumption1 M D prm.LV → Assumption2 M D prm.Lr prm.LT →
      IsRun M P choose play (statesMB P prm choose) prm.K μ traj →
      1 - 2 * prm.δ ≤ (μ {ω | ∀ k ∈ Finset.Icc 1 prm.K, ∀ h : Fin H,
        (∀ B, isActive P (statesMB P prm choose (traj ω) k h) B → ∀ p ∈ P.region B,
          0 ≤ (statesMB P prm choose (traj ω) k h).Q B - optQ M h p ∧
          ((∀ (x x' : S) (a : A), dist x x' ≤ D (x, a) (x', a)) →
            (statesMB P prm choose (traj ω) k h).Q B - optQ M h p ≤
              2 * prm.rucbMB ((statesMB P prm choose (traj ω) k h).n B) + 2 * prm.tucbMB ((statesMB P prm choose (traj ω) k h).n B) +
                CL * prm.biasMB (P.diam B) + ((if hh : h.val + 1 < H then ∫ y, VbarMB P prm ((statesMB P prm choose (traj ω) k) ⟨h.val + 1, hh⟩) y ∂(M.T h p) else 0) - ∫ y, optVRem M (H - 1 - h.val) y ∂(M.T h p)))) ∧
        (∀ x, 0 ≤ VbarMB P prm (statesMB P prm choose (traj ω) k h) x - optV M h x) ∧
        (∀ X ∈ minCells P (statesMB P prm choose (traj ω) k h), ∀ x ∈ X, 0 ≤ (statesMB P prm choose (traj ω) k h).Vt X - optV M h x) ∧
        ((∀ (x x' : S) (a : A), dist x x' ≤ D (x, a) (x', a)) →
          VbarMB P prm (statesMB P prm choose (traj ω) (k - 1) h) ((traj ω k).1 h.castSucc) ≤
            (statesMB P prm choose (traj ω) (k - 1) h).Q (selAt P choose (statesMB P prm choose) (traj ω) k h) + prm.LV * P.diam (selAt P choose (statesMB P prm choose) (traj ω) k h))}).toReal) := by sorry

end AdaDiscRL
