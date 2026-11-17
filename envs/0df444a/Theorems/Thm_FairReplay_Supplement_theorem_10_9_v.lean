-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_9_v
-- name    : FairReplay.Supplement.theorem_10_9_v
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:02:20.38852+00:00
-- url     : https://prove2.me/theorems/bde07305-56a5-4df7-a2a9-93cd02fcf2ec
-- title:
--   Theorem 10.9(v) — fixed-design hybrid tester with cost $\le N_U\sum_{x\in U}\bar c_x+L C^{A\setminus U}_{\mathrm{ctrl}}+\sum_{q^\star_i>0}c_i$
-- statement:
--   Fix a declared two-class family with $U\neq\varnothing$ in which every candidate is observable, $m=|U|$, $p,s,\tau>0$ with $p+s+\tau<1$ and $\delta\in(0,1/2)$. The minimum defining $C^{A\setminus U}_{\mathrm{ctrl}}$ is attained, and the following holds for every optimizer $q^\star$.
--
--   1. For every $d>0$ with $p+s+\tau+d<1$ there is a fixed-design hybrid tester with type-I error and every pointwise type-II error at most $\delta$, and declared cost at most
--   $$N_U\sum_{x\in U}\bar c_x+L\,C^{A\setminus U}_{\mathrm{ctrl}}+\sum_{i:\,q^\star_i>0}c_i,\qquad N_U=\Big\lceil\frac{8(\tau+d)}{d^2}\log\frac m\delta\Big\rceil,\quad L=\Big\lceil\frac{\log\delta}{\log(1-d)}\Big\rceil.$$
--   2. Consequently the lower program of (i) and this upper bound both lie within constant factors of $d^{-2}\sum_{x\in U}\bar c_x$ for all small $d$: they match the $d^{-2}$ leading order and the boundary-minimum/control-cover cost geometry up to constants.
--
--   Differences from the source:
--   - reading: q⋆ ("an optimizer", not specified) → the conclusion holds for every optimizer q⋆ of the cover program; reason: the stronger of the two readings (for some vs. every optimizer); every optimizer gives a valid schedule
--   - encoding: L·C_ctrl → L · Σ_i c_i q⋆_i; reason: equal, since q⋆ attains the cover program's value
--   - encoding: fixed-design tester → IsFixedDesign: round t plays a schedule sched t independent of the history, and T ≡ N; reason: a deterministic schedule fixed in advance with a fixed number of queries
--   - reading: the mixed lower and upper bounds match the d⁻² leading order and cost geometry up to constants → ∃ c₁, C₁, d₀ > 0: c₁ Σ_U c̄_x/d² ≤ QLB(d) and (72) ≤ C₁ Σ_U c̄_x/d² for d ∈ (0, d₀); reason: both sides are compared with the same boundary-minimum quantity Σ_U c̄_x/d²; constants depend on the fixed topology and p, s, τ, δ
--   - encoding: the declared two-class family (vertices low/high, candidates A, legal groups S_i with |S_i| ≥ 2, costs c_i > 0) → a TwoClassFamily structure on Fin n whose first k actions query the k groups and whose final deterministic zero-cost action represents making no query; a query of S_i reveals the coded ordered old/new outputs of its members on one fresh tape; reason: direct transcription of §10.5; the idle action carries no information and keeps the zero-query tester expressible when k = 0; coordinates outside S_i are constant
--   - encoding: δ-correct (pointwise type-II error) → IsGroupDeltaCorrect: type I ≤ δ under the simple null and type II ≤ δ under every alternative x ∈ A; reason: the paper's "type-I error and every pointwise type-II error at most δ"
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.9(v), eqs. (72)–(73), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_armCount
import Definitions.Def_FairReplay_Supplement_TwoClassFamily
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_coverLP
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_QLB
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_Qstar0
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_Bcap

open MeasureTheory

namespace FairReplay.Supplement

open TwoClassFamily

/-- **Theorem 10.9(v), the fixed-design hybrid tester, eqs. (72)–(73)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.9(v), p.20
(PDF p.22)): "(v) Suppose U ≠ ∅ and every candidate is observable, and let m = |U|. There is a
fixed-design hybrid tester with type-I error and every pointwise type-II error at most δ, and declared
cost at most NU Σ_{x∈U} c̄x + L C^{A\U}_ctrl + Σ_{i:q⋆_i>0} ci, (72) where NU = ⌈8(τ + d)/d² log m/δ⌉,
L = ⌈log δ / log(1 − d)⌉, (73) and q⋆ is an optimizer defining C^{A\U}_ctrl. Consequently, for every
fixed finite topology and fixed τ > 0, the mixed lower and upper bounds match the d−2 leading order
and the boundary-minimum/control-cover cost geometry up to constants."

For a declared two-class family `F` with `U ≠ ∅` in which every candidate is observable, fixed
`p, s, τ > 0` with `p + s + τ < 1`, `δ ∈ (0, 1/2)`, `m = |U|` and any optimizer `q⋆` of the control-cover
program on `A ∖ U`:
0. the control-cover program on `A ∖ U` has an optimizer;
1. for every `d > 0` with `p + s + τ + d < 1` there is a fixed-design tester with type-I error `≤ δ` and
   type-II error `≤ δ` under every `x ∈ A`, whose declared cost is, on every run, at most
   `N_U Σ_{x∈U} c̄_x + L C^{A∖U}_ctrl + Σ_{i : q⋆_i > 0} c_i`, `N_U = ⌈8(τ + d) log(m/δ)/d²⌉`,
   `L = ⌈log δ / log(1 − d)⌉`;
2. there are `c₁, C₁, d₀ > 0` with `c₁ Σ_{x∈U} c̄_x / d² ≤ QLB(d)` and (72) `≤ C₁ Σ_{x∈U} c̄_x / d²` for
   every `d ∈ (0, d₀)`.

**Formalization Note** `L C^{A∖U}_ctrl` is written `L · Σ_i c_i q⋆_i` (equal). "Match up to constants" is
read as item 2: the lower program and the bound (72) are both within constant factors of
`Σ_{x∈U} c̄_x / d²`, constants depending on the fixed topology and `p, s, τ, δ`. -/
theorem theorem_10_9_v (F : TwoClassFamily) (p s τ δ : ℝ) (hp : 0 < p) (hs : 0 < s) (hτ : 0 < τ)
    (hpst : p + s + τ < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (hU : F.unmatched.Nonempty)
    (hobs : ∀ x ∈ F.A, F.Observable x) :
    (∃ q : Fin F.k → ℝ, F.IsCoverOptimizer (F.A \ F.unmatched) q) ∧
      ∀ q : Fin F.k → ℝ, F.IsCoverOptimizer (F.A \ F.unmatched) q →
        (∀ d : ℝ, 0 < d → p + s + τ + d < 1 →
          ∃ (π : BanditAlgorithm.BanditPolicy (F.k + 1))
            (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
            (ψ : (ℕ → Fin (F.k + 1) × ℝ) → Bool)
            (hT : BanditAlgorithm.IsBanditStoppingTime T),
            Measurable[hT.measurableSpace] ψ ∧ IsFixedDesign π T ∧
            F.IsGroupDeltaCorrect p s τ d δ π T ψ ∧
            ∀ ω, F.declaredCost T ω ≤
              ENNReal.ofReal (⌈8 * (τ + d) / d ^ 2 * Real.log (F.unmatched.card / δ)⌉₊ *
                  ∑ x ∈ F.unmatched, F.cbar x +
                ⌈Real.log δ / Real.log (1 - d)⌉₊ * ∑ i, F.c i * q i + F.supportCost q)) ∧
        ∃ c₁ C₁ d₀ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < d₀ ∧ d₀ ≤ 1 - p - s - τ ∧
          ∀ d : ℝ, 0 < d → d < d₀ →
            ENNReal.ofReal (c₁ * (∑ x ∈ F.unmatched, F.cbar x) / d ^ 2) ≤
                F.QLB p s τ d δ ∧
            (⌈8 * (τ + d) / d ^ 2 * Real.log (F.unmatched.card / δ)⌉₊ *
                  ∑ x ∈ F.unmatched, F.cbar x +
                ⌈Real.log δ / Real.log (1 - d)⌉₊ * ∑ i, F.c i * q i + F.supportCost q) ≤
              C₁ * (∑ x ∈ F.unmatched, F.cbar x) / d ^ 2 := by sorry

end FairReplay.Supplement
