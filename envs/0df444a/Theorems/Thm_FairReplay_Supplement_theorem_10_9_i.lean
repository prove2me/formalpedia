-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_9_i
-- name    : FairReplay.Supplement.theorem_10_9_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:58:47.039146+00:00
-- url     : https://prove2.me/theorems/12e73426-2719-421b-a487-f6afef1c0ab9
-- title:
--   Theorem 10.9(i) — $\mathbb E_0[\mathrm{cost}]\ge\min_{n\ge0}\{c^\top n:(K_{\mathrm{ctrl}}C+K_{\mathrm{bnd}}R)n\ge\mathrm{kl}(1-\delta,\delta)\mathbf 1\}$
-- statement:
--   Fix a declared two-class family (legal groups $S_i$ with $|S_i|\ge2$ and costs $c_i>0$; candidates $A$), $p,s,\tau,d>0$ with $p+s+\tau+d<1$ and $\delta\in(0,1/2)$. Every adaptive partial-replay tester that is $\delta$-correct (type I at most $\delta$ under the simple null, type II at most $\delta$ under every alternative $x\in A$) and has finite expected null declared cost satisfies
--   $$\mathbb E_0[\mathrm{cost}]\ \ge\ \min_{n\ge 0}\Big\{c^\top n:\ (K_{\mathrm{ctrl}}C+K_{\mathrm{bnd}}R)\,n\ \ge\ \mathrm{kl}(1-\delta,\delta)\,\mathbf 1\Big\},$$
--   where $C$ marks control groups (containing $x$ and another high vertex), $R$ boundary-only groups (containing $x$ and no other high vertex), $K_{\mathrm{ctrl}}=r\log\frac r{r-d}$, $K_{\mathrm{bnd}}=\tau\log\frac\tau{\tau+d}+r\log\frac r{r-d}$ and $r=1-p-s-\tau$.
--
--   The program says that each candidate must accumulate $\mathrm{kl}(1-\delta,\delta)$ nats of information, at rate $K_{\mathrm{ctrl}}\approx d$ per control query and $K_{\mathrm{bnd}}\approx d^2$ per boundary query.
--
--   Differences from the source:
--   - encoding: C and R (described in words only) → C_{x,i} = 1 iff x ∈ S_i and S_i contains another high vertex; R_{x,i} = 1 iff x ∈ S_i and S_i contains no other high vertex; reason: the definitions used in the proof of (i), p.21
--   - encoding: min over n ≥ 0 of the lower program → QLB: infimum over real n ≥ 0, in [0, ∞] (∞ when infeasible); reason: the minimum when feasible; ∞ matches the absence of any δ-correct finite-cost tester
--   - encoding: the declared two-class family (vertices low/high, candidates A, legal groups S_i with |S_i| ≥ 2, costs c_i > 0) → a TwoClassFamily structure on Fin n whose first k actions query the k groups and whose final deterministic zero-cost action represents making no query; a query of S_i reveals the coded ordered old/new outputs of its members on one fresh tape; reason: direct transcription of §10.5; the idle action carries no information and keeps the zero-query tester expressible when k = 0; coordinates outside S_i are constant
--   - encoding: declared cost, E₀[cost] → Σ_i c_i N_i with N_i = armCount i T (queries of group i before stopping), expectation a lower integral in [0, ∞]; reason: declared cost charges c_i per query of S_i
--   - encoding: δ-correct (pointwise type-II error) → IsGroupDeltaCorrect: type I ≤ δ under the simple null and type II ≤ δ under every alternative x ∈ A; reason: the paper's "type-I error and every pointwise type-II error at most δ"
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §10.5 and Theorem 10.9(i), eq. (65), pp.18–19 (PDF pp.20–21)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_armCount
import Definitions.Def_FairReplay_Supplement_TwoClassFamily
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_coverLP
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_QLB
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_Qstar0

open MeasureTheory

namespace FairReplay.Supplement

open TwoClassFamily

/-- **Theorem 10.9(i), the information lower program, eq. (65)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), §10.5 and Theorem 10.9(i),
pp.18–19 (PDF pp.20–21)): "Fix δ ∈ (0, 1/2) and the declared two-class family above. (i) Every adaptive
δ-correct partial-replay tester with finite null expected declared cost satisfies
E0[cost] ≥ min_{n≥0} { c⊤n : (KctrlC + KbndR) n ≥ kl(1 − δ, δ)1 }. (65)"

Throughout, `F` is a declared two-class family (vertices low or high, candidates `A` ⊆ high, legal groups `S_i` with `|S_i| ≥ 2` and costs `c_i > 0`), `p, s, τ, d > 0` with `p + s + τ + d < 1`, `r = 1 − p − s − τ`, and `δ ∈ (0, 1/2)`. Under the simple null all old thresholds are `p`, low new thresholds `p + s`, high new thresholds `p + s + τ`; alternative `x ∈ A` raises only `x`'s new threshold by `d`.

Every adaptive partial-replay tester `(π, T, ψ)` that is δ-correct (type I `≤ δ` under the null, type II
`≤ δ` under every `x ∈ A`) and whose expected null declared cost `E₀[Σ_i c_i N_i]` is finite satisfies
`E₀[cost] ≥ QLB(d) = min_{n ≥ 0} { c⊤n : Σ_i (K_ctrl C_{x,i} + K_bnd R_{x,i}) n_i ≥ kl(1 − δ, δ) ∀ x ∈ A }`,
where `C_{x,i} = 1` iff `S_i` contains `x` and another high vertex, `R_{x,i} = 1` iff `S_i` contains `x` and no
other high vertex, `K_ctrl = r log(r/(r − d))` and `K_bnd = τ log(τ/(τ + d)) + r log(r/(r − d))`.

**Formalization Note** `C` and `R` are read from the proof of (i) (p.21), the paper's only definition
of them. The lower program is an infimum in `[0, ∞]` (`∞` when infeasible). Actions are the legal
groups; the stopping time is named `T`. -/
theorem theorem_10_9_i (F : TwoClassFamily) (p s τ d δ : ℝ) (hp : 0 < p) (hs : 0 < s)
    (hτ : 0 < τ) (hd : 0 < d) (hsum : p + s + τ + d < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2)
    (π : BanditAlgorithm.BanditPolicy (F.k + 1)) (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin (F.k + 1) × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T)
    (hψ : Measurable[hT.measurableSpace] ψ) (hcorr : F.IsGroupDeltaCorrect p s τ d δ π T ψ)
    (hfin : ∫⁻ ω, F.declaredCost T ω
      ∂BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d none) π < ⊤) :
    F.QLB p s τ d δ ≤
      ∫⁻ ω, F.declaredCost T ω ∂BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d none) π := by sorry

end FairReplay.Supplement
