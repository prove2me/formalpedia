-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_9_ii
-- name    : FairReplay.Supplement.theorem_10_9_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:59:35.464225+00:00
-- url     : https://prove2.me/theorems/2c8dc7b5-8208-4d08-ad1a-9d31c6ba717f
-- title:
--   Theorem 10.9(ii) — matched controls: a zero-type-I fixed design with cost $\le L\,C_{\mathrm{ctrl}}+\sum_{q^\star_i>0}c_i$
-- statement:
--   Fix a declared two-class family, $p,s,\tau,d>0$ with $p+s+\tau+d<1$ and $\delta\in(0,1/2)$. Let
--   $$C_{\mathrm{ctrl}}=\min_{q\ge0}\big\{c^\top q:\ Cq\ge\mathbf 1\big\}$$
--   be the fractional control-cover quantity. If $C_{\mathrm{ctrl}}<\infty$, the minimum is attained and, for every optimizer $q^\star$, there is a fixed-design tester with zero type-I error and type-II error at most $\delta$ under every alternative $x\in A$, whose declared cost is at most
--   $$L\,C_{\mathrm{ctrl}}+\sum_{i:\,q^\star_i>0}c_i,\qquad L=\Big\lceil\frac{\log\delta}{\log(1-d)}\Big\rceil.$$
--
--   Matched same-background controls thus restore the linear $d^{-1}$ replay channel despite the benign class shift $\tau$.
--
--   Differences from the source:
--   - reading: q⋆ ("an optimizer", not specified) → the conclusion holds for every optimizer q⋆ of the cover program; reason: the stronger of the two readings (for some vs. every optimizer); every optimizer gives a valid schedule
--   - encoding: L·C_ctrl → L · Σ_i c_i q⋆_i; reason: equal, since q⋆ attains the cover program's value
--   - encoding: fixed-design tester → IsFixedDesign: round t plays a schedule sched t independent of the history, and T ≡ N; reason: a deterministic schedule fixed in advance with a fixed number of queries
--   - encoding: declared cost at most … → the bound holds on every run; reason: a fixed design has a deterministic cost
--   - encoding: the declared two-class family (vertices low/high, candidates A, legal groups S_i with |S_i| ≥ 2, costs c_i > 0) → a TwoClassFamily structure on Fin n whose first k actions query the k groups and whose final deterministic zero-cost action represents making no query; a query of S_i reveals the coded ordered old/new outputs of its members on one fresh tape; reason: direct transcription of §10.5; the idle action carries no information and keeps the zero-query tester expressible when k = 0; coordinates outside S_i are constant
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.9(ii), eqs. (66)–(67), p.19 (PDF p.21)

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

/-- **Theorem 10.9(ii), the matched-control fixed design, eqs. (66)–(67)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.9(ii),
p.19 (PDF p.21)): "(ii) Define the fractional control-cover quantity Cctrl = min_{q≥0} { c⊤q : Cq ≥ 1 }.
(66) If Cctrl < ∞, a fixed-design tester has zero type-I error and pointwise type-II error at most δ
using declared cost at most L Cctrl + Σ_{i:q⋆_i>0} ci, L = ⌈log δ / log(1 − d)⌉. (67)"

Throughout, `F` is a declared two-class family (vertices low or high, candidates `A` ⊆ high, legal groups `S_i` with `|S_i| ≥ 2` and costs `c_i > 0`), `p, s, τ, d > 0` with `p + s + τ + d < 1`, `r = 1 − p − s − τ`, and `δ ∈ (0, 1/2)`. Under the simple null all old thresholds are `p`, low new thresholds `p + s`, high new thresholds `p + s + τ`; alternative `x ∈ A` raises only `x`'s new threshold by `d`.

If `C_ctrl < ∞`, the control-cover program has an optimizer, and for every optimizer `q⋆` there is a fixed-design
tester (deterministic schedule, fixed number of rounds) that never rejects under the null, fails to
reject with probability at most `δ` under every alternative `x ∈ A`, and whose declared cost is, on
every run, at most `L C_ctrl + Σ_{i : q⋆_i > 0} c_i` with `L = ⌈log δ / log(1 − d)⌉`.

**Formalization Note** `L C_ctrl` is written `L · Σ_i c_i q⋆_i` (equal, since `q⋆` attains `C_ctrl`).
"For every optimizer" is the reading of "q⋆" (the paper does not say which optimizer). -/
theorem theorem_10_9_ii (F : TwoClassFamily) (p s τ d δ : ℝ) (hp : 0 < p) (hs : 0 < s)
    (hτ : 0 < τ) (hd : 0 < d) (hsum : p + s + τ + d < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2)
    (hC : F.Cctrl < ⊤) :
    (∃ q : Fin F.k → ℝ, F.IsCoverOptimizer F.A q) ∧
      ∀ q : Fin F.k → ℝ, F.IsCoverOptimizer F.A q →
        ∃ (π : BanditAlgorithm.BanditPolicy (F.k + 1))
          (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
          (ψ : (ℕ → Fin (F.k + 1) × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T),
          Measurable[hT.measurableSpace] ψ ∧ IsFixedDesign π T ∧
          BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d none) π
              {ω | T ω < ⊤ ∧ ψ ω = true} = 0 ∧
          (∀ x ∈ F.A, BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d (some x)) π
              {ω | ¬ (T ω < ⊤ ∧ ψ ω = true)} ≤ ENNReal.ofReal δ) ∧
          ∀ ω, F.declaredCost T ω ≤
            ENNReal.ofReal
              (⌈Real.log δ / Real.log (1 - d)⌉₊ * ∑ i, F.c i * q i + F.supportCost q) := by sorry

end FairReplay.Supplement
