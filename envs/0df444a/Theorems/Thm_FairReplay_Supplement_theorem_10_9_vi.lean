-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_9_vi
-- name    : FairReplay.Supplement.theorem_10_9_vi
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:03:20.222714+00:00
-- url     : https://prove2.me/theorems/1bb8a046-04d6-4cd6-9300-c7a0a45b785a
-- title:
--   Theorem 10.9(vi) — sequential hybrid tester without the $\log m$ factor; $\frac a{b_2}\sum\bar c_x\le\liminf d^2Q^\star_0\le\limsup d^2Q^\star_0\le\frac{\log(1/\delta)}{b_2}\sum\bar c_x$
-- statement:
--   Fix a declared two-class family with $U\neq\varnothing$ in which every candidate is observable, $m=|U|$, $p,s,\tau>0$ with $p+s+\tau<1$, $r=1-p-s-\tau$, $\delta\in(0,1/2)$ and $a=\mathrm{kl}(1-\delta,\delta)$. The minimum defining $C^{A\setminus U}_{\mathrm{ctrl}}$ is attained. With $J_{\mathrm{bnd}}$, $H_0$, $H_1$ as in (74)–(75), the following holds for every optimizer $q^\star$:
--
--   1. for every $d>0$ with $p+s+\tau+d<1$ there is a sequential hybrid tester with type-I error and every pointwise type-II error at most $\delta$, whose expected null declared cost is at most
--   $$H_0\sum_{x\in U}\bar c_x+L\,C^{A\setminus U}_{\mathrm{ctrl}}+\sum_{i:\,q^\star_i>0}c_i,$$
--   and whose expected boundary-block cost under every alternative $x\in U$ is at most $H_0\sum_{z\in U\setminus\{x\}}\bar c_z+H_1\bar c_x$;
--   2. the optimal expected null declared cost $Q^\star_0(d)$ satisfies
--   $$\frac{a}{b_2}\sum_{x\in U}\bar c_x\ \le\ \liminf_{d\downarrow0}d^2Q^\star_0(d)\ \le\ \limsup_{d\downarrow0}d^2Q^\star_0(d)\ \le\ \frac{\log(1/\delta)}{b_2}\sum_{x\in U}\bar c_x;$$
--   3. the remaining multiplicative gap is $\log(1/\delta)/\mathrm{kl}(1-\delta,\delta)$, which depends only on the confidence and is approximately $1.1305$ at $\delta=0.05$.
--
--   Differences from the source:
--   - reading: q⋆ ("an optimizer", not specified) → the conclusion holds for every optimizer q⋆ of the cover program; reason: the stronger of the two readings (for some vs. every optimizer); every optimizer gives a valid schedule
--   - encoding: L·C_ctrl → L · Σ_i c_i q⋆_i; reason: equal, since q⋆ attains the cover program's value
--   - encoding: expected boundary-block cost → expected declared cost on the groups that meet U; reason: the boundary block of the hybrid tester queries exactly such groups; they contain no other high vertex
--   - encoding: lim inf / lim sup of d² Q⋆₀(d) as d ↓ 0 → liminf / limsup in [0, ∞] along 𝓝[>] 0; reason: Q⋆₀ may be ∞
--   - reading: the remaining gap depends only on confidence: log(1/δ)/kl(1−δ, δ), approximately 1.1305 at δ = 0.05 → the ratio of the two ends of (78) equals log(1/δ)/kl(1−δ, δ), and |log 20/kl(0.95, 0.05) − 1.1305| < 10⁻⁴; reason: "approximately" read as agreement to the four printed decimals
--   - encoding: the declared two-class family (vertices low/high, candidates A, legal groups S_i with |S_i| ≥ 2, costs c_i > 0) → a TwoClassFamily structure on Fin n whose first k actions query the k groups and whose final deterministic zero-cost action represents making no query; a query of S_i reveals the coded ordered old/new outputs of its members on one fresh tape; reason: direct transcription of §10.5; the idle action carries no information and keeps the zero-query tester expressible when k = 0; coordinates outside S_i are constant
--   - encoding: declared cost, E₀[cost] → Σ_i c_i N_i with N_i = armCount i T (queries of group i before stopping), expectation a lower integral in [0, ∞]; reason: declared cost charges c_i per query of S_i
--   - encoding: δ-correct (pointwise type-II error) → IsGroupDeltaCorrect: type I ≤ δ under the simple null and type II ≤ δ under every alternative x ∈ A; reason: the paper's "type-I error and every pointwise type-II error at most δ"
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.9(vi), eqs. (74)–(79), pp.20–21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_armCount
import Definitions.Def_FairReplay_Supplement_TwoClassFamily
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_coverLP
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_QLB
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_Qstar0
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_Bcap

open MeasureTheory Filter Topology

namespace FairReplay.Supplement

open TwoClassFamily

/-- **Theorem 10.9(vi), the sequential hybrid tester and the bracket, eqs. (74)–(79)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem
10.9(vi), pp.20–21 (PDF pp.22–23)): "(vi) The multiplicative log m term can be removed from the expected
null cost by allowing an unbounded sequential stopping time. Define the reverse boundary divergence
Jbnd(τ, d) = (τ + d) log((τ + d)/τ) + (r − d) log((r − d)/r), (74) and H0 = (log(1/δ) + log(r/(r −
d)))/Kbnd(τ, d), H1 = (log(m/δ) + log(1 + d/τ))/Jbnd(τ, d). (75) There is a sequential hybrid tester
with type-I error and every pointwise type-II error at most δ, whose expected null declared cost is at
most H0 Σ_{x∈U} c̄x + L C^{A\U}_ctrl + Σ_{i:q⋆_i>0} ci. (76) Under singleton alternative x ∈ U, its expected
boundary-block cost is at most H0 Σ_{z∈U\{x}} c̄z + H1 c̄x. (77) [...] if Q⋆0(d) denotes the optimal
expected null declared cost in this P19 family and a = kl(1 − δ, δ), then a/b2 Σ_{x∈U} c̄x ≤ lim inf_{d↓0}
d²Q⋆0(d) ≤ lim sup_{d↓0} d²Q⋆0(d) ≤ log(1/δ)/b2 Σ_{x∈U} c̄x. (78) The remaining multiplicative gap depends
only on confidence: log(1/δ)/kl(1 − δ, δ). (79) It is independent of topology size and equals
approximately 1.1305 at δ = 0.05."

For a declared two-class family `F` with `U ≠ ∅` in which every candidate is observable, fixed
`p, s, τ > 0` with `p + s + τ < 1`, `δ ∈ (0, 1/2)`, `m = |U|` and any optimizer `q⋆` of the control-cover
program on `A ∖ U`:
0. the control-cover program on `A ∖ U` has an optimizer;
1. for every `d > 0` with `p + s + τ + d < 1` there is an adaptive tester with type-I error `≤ δ` and
   type-II error `≤ δ` under every `x ∈ A`, whose expected null declared cost is at most
   `H0 Σ_{x∈U} c̄_x + L C^{A∖U}_ctrl + Σ_{i : q⋆_i > 0} c_i`, and whose expected boundary-block cost under
   every alternative `x ∈ U` is at most `H0 Σ_{z∈U∖{x}} c̄_z + H1 c̄_x`;
2. (78) `a/b2 Σ_{x∈U} c̄_x ≤ liminf_{d↓0} d² Q⋆₀(d) ≤ limsup_{d↓0} d² Q⋆₀(d) ≤ log(1/δ)/b2 Σ_{x∈U} c̄_x`;
3. (79) the ratio of the two ends of (78) is `log(1/δ)/kl(1 − δ, δ)`, and at `δ = 0.05` this number is
   within `10⁻⁴` of `1.1305`.

**Formalization Note** The boundary-block cost is the declared cost on groups meeting `U`. `Q⋆₀(d)` is in
`[0, ∞]` and the bracket is a liminf/limsup in `ℝ≥0∞` along `d → 0⁺`. `L C^{A∖U}_ctrl` is written
`L · Σ_i c_i q⋆_i`. -/
theorem theorem_10_9_vi (F : TwoClassFamily) (p s τ δ : ℝ) (hp : 0 < p) (hs : 0 < s) (hτ : 0 < τ)
    (hpst : p + s + τ < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (hU : F.unmatched.Nonempty)
    (hobs : ∀ x ∈ F.A, F.Observable x) :
    (∃ q : Fin F.k → ℝ, F.IsCoverOptimizer (F.A \ F.unmatched) q) ∧
      (∀ q : Fin F.k → ℝ, F.IsCoverOptimizer (F.A \ F.unmatched) q →
        ∀ d : ℝ, 0 < d → p + s + τ + d < 1 →
          ∃ (π : BanditAlgorithm.BanditPolicy (F.k + 1))
            (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
            (ψ : (ℕ → Fin (F.k + 1) × ℝ) → Bool)
            (hT : BanditAlgorithm.IsBanditStoppingTime T),
            Measurable[hT.measurableSpace] ψ ∧ F.IsGroupDeltaCorrect p s τ d δ π T ψ ∧
            ∫⁻ ω, F.declaredCost T ω
                ∂BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d none) π ≤
              ENNReal.ofReal (H0 p s τ d δ * ∑ x ∈ F.unmatched, F.cbar x +
                ⌈Real.log δ / Real.log (1 - d)⌉₊ * ∑ i, F.c i * q i + F.supportCost q) ∧
            ∀ x ∈ F.unmatched,
              ∫⁻ ω, F.boundaryCost T ω
                  ∂BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d (some x)) π ≤
                ENNReal.ofReal (H0 p s τ d δ * ∑ z ∈ F.unmatched.erase x, F.cbar z +
                  H1 p s τ d δ F.unmatched.card * F.cbar x)) ∧
      ENNReal.ofReal (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ / b2 p s τ *
          ∑ x ∈ F.unmatched, F.cbar x) ≤
        liminf (fun d => ENNReal.ofReal (d ^ 2) * F.Qstar0 p s τ d δ) (𝓝[>] 0) ∧
      liminf (fun d => ENNReal.ofReal (d ^ 2) * F.Qstar0 p s τ d δ) (𝓝[>] 0) ≤
        limsup (fun d => ENNReal.ofReal (d ^ 2) * F.Qstar0 p s τ d δ) (𝓝[>] 0) ∧
      limsup (fun d => ENNReal.ofReal (d ^ 2) * F.Qstar0 p s τ d δ) (𝓝[>] 0) ≤
        ENNReal.ofReal (Real.log (1 / δ) / b2 p s τ * ∑ x ∈ F.unmatched, F.cbar x) ∧
      (Real.log (1 / δ) / b2 p s τ * ∑ x ∈ F.unmatched, F.cbar x) /
          (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ / b2 p s τ *
            ∑ x ∈ F.unmatched, F.cbar x) =
        Real.log (1 / δ) / BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ ∧
      |Real.log (1 / (0.05 : ℝ)) / BanditAlgorithm.bernoulliRelativeEntropy (1 - 0.05) 0.05 -
          1.1305| < 1 / 10000 := by sorry

end FairReplay.Supplement
