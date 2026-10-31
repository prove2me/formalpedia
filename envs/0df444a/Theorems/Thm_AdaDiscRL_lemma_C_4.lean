-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_C_4
-- name    : AdaDiscRL.lemma_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:21.266663+00:00
-- url     : https://prove2.me/theorems/a4ae4d65-3191-4933-9600-2e00286535b9
-- title:
--   Lemma C.4 — Wasserstein concentration of the AdaMB transition estimates (corrected: $L_V$ placement; $\mathcal D_{\mathcal S}\le\mathcal D$)
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Under Assumption 2, for a run of AdaMB that uses this $c$ in its bonus and $L_V>0$, in a metric with $\mathcal D_{\mathcal S}(x,x')\le\mathcal D((x,a),(x',a))$: with probability at least $1-\delta$, for every episode $k\in[K]$, step $h$, active ball $B\in\mathcal P^k_h$ and $(x,a)\in B$, the estimate $\overline{\mathbf T}^k_h(\cdot\mid B)$ (mass $\overline{\mathbf T}^k_h(A\mid B)$ at the center $\tilde x(A)$ of each state cell $A$) is a probability measure and
--   $$
--   d_W\big(\overline{\mathbf T}^k_h(\cdot\mid B),T_h(\cdot\mid x,a)\big)\le\frac{\mathrm{Tucb}^k_h(B)}{L_V}+(5L_T+4)\,\mathrm{diam}(B).
--   $$
--   This bounds the error of the model-based backup in Eq. (6).
--
--   Differences from the source:
--   - correction: d_W ≤ (1/L_V)(Tucb + (5L_T + 4) diam(B)) → d_W ≤ Tucb/L_V + (5L_T + 4) diam(B); reason: the proof (p.67) ends (4 + 5L_T) diam + d_W(…), losing L_V on the first term; with T ≡ δ₀ on S = [0,1]^{d_S} the left side is diam(B)/2 at every level while the printed right side is O(diam(B) polylog/L_V) for large L_V (correction C7)
--   - correction: Lemma C.4 for AdaMB with any metric D ≤ D_S + D_A → AdaMB part assumes D_S(x, x′) ≤ D((x, a), (x′, a)); reason: counterexample: S = [0, s], A a point, D = D_S/s (an admissible metric with diameter 1), T ≡ δ₀, r ≡ 0; V̄ and T̄ use D_S-distances to cell centers that are (s/2)·diam(B), which breaks the bound for large s
--   - reading: c an absolute constant in Tucb (p.17) → ∃ c > 0 quantified before all types, and the run uses prm.c = c; reason: the paper fixes c once (reading R4)
--   - encoding: 1/L_V → 0 < L_V; reason: the printed bound divides by L_V
--   - encoding: T̄(· | B) a distribution over the cells of level ℓ(B) → the discrete measure Σ_A T̄(A | B) δ_{x̃(A)}, asserted to be a probability measure; d_W = WassersteinLinOpt.Ball.wassersteinDist 1; reason: p.17 identifies T̄ with sampling over the centers; d_W is defined on probability measures
--   - generalization: AdaMB/AdaQL run with a given sequence of starting states {X_1^k}, action ã(B_h^k) (or a distribution on the ball), argmax with ties, rewards and transitions drawn from R_h and T_h → IsRun: starting states arbitrary random variables, action law any kernel supported on the ball's action cell, any argmax rule, only the conditional marginals of R_h^k and X_{h+1}^k fixed; reason: each choice of the source is a special case (reading R8); the statement holds for every such run
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma C.4, p.42 (= Lemma J.3, pp.63–67)

import Mathlib
import Definitions.Def_AdaDiscRL_adaMB
import Definitions.Def_AdaDiscRL_IsRun
import Definitions.Def_AdaDiscRL_Assumption2
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma C.4 (Concentration of Transition for AdaMB)** (arXiv:2110.15843v3, p.42; = Lemma J.3,
pp.63–67), corrected. There is an absolute constant `c > 0` (the constant of `Tucb`) such that under
Assumption 2, for a run of AdaMB with that `c` and `L_V > 0`, in a metric `D` that dominates `D_S`
on each action section, with probability at least `1 − δ`, for every `(h, k)`, active `B ∈ P_h^k`
and `(x, a) ∈ B`: `T̄_h^k(· | B)` (the discrete law putting mass `T̄_h^k(A | B)` on the center `x̃(A)`
of each cell `A`) is a probability measure and
`d_W(T̄_h^k(· | B), T_h(· | x, a)) ≤ Tucb_h^k(B)/L_V + (5 L_T + 4) diam(B)`.

**Formalization Note.** Corrections: (i) the printed `(1/L_V)(Tucb + (5L_T + 4) diam)` loses `L_V`
on the second term (the proof, p.67, ends with `(4 + 5L_T) diam + d_W(…)`); with `T ≡ δ₀` on
`S = [0,1]^{d_S}` the left side is `diam(B)/2` at every level while the printed right side is
`O(diam(B) polylog/L_V)`. (ii) `D_S(x, x′) ≤ D((x, a), (x′, a))` is added: with `S = [0, s]`, `A` a
point, `D = D_S/s`, `T ≡ δ₀`, all mass of `T̄` sits on centers at `D_S`-distance `≥ (s/2) diam(B)` from
`0`, which exceeds the bound for `s > 9` and large `L_V`. `d_W` is
`WassersteinLinOpt.Ball.wassersteinDist 1`. -/
theorem lemma_C_4 : ∃ c : ℝ, 0 < c ∧
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
    prm.c = c → 0 < prm.LV → Assumption2 M D prm.Lr prm.LT →
    (∀ (x x' : S) (a : A), dist x x' ≤ D (x, a) (x', a)) →
    IsRun M P choose play (statesMB P prm choose) prm.K μ traj →
    1 - prm.δ ≤ (μ {ω | ∀ k ∈ Finset.Icc 1 prm.K, ∀ h : Fin H, ∀ B, isActive P (statesMB P prm choose (traj ω) k h) B →
      ∀ p ∈ P.region B, ∃ ν : ProbabilityMeasure S, (ν : Measure S) = Measure.sum (fun X : Set S => ENNReal.ofReal ((statesMB P prm choose (traj ω) k h).Tbar B X) • Measure.dirac (P.sCenter X)) ∧
        WassersteinLinOpt.Ball.wassersteinDist 1 ν ⟨M.T h p, (M.isMarkov_T h).isProbabilityMeasure p⟩ ≤
          ENNReal.ofReal (prm.tucbMB ((statesMB P prm choose (traj ω) k h).n B) / prm.LV + (5 * prm.LT + 4) * P.diam B)}).toReal := by sorry

end AdaDiscRL
