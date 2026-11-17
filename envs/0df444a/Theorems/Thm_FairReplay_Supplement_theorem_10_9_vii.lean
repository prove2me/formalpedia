-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_9_vii
-- name    : FairReplay.Supplement.theorem_10_9_vii
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:04:14.637659+00:00
-- url     : https://prove2.me/theorems/3e47c843-7112-4ca9-bac6-19d0b158ba05
-- title:
--   Theorem 10.9(vii) — Markov truncation: type I $\le\eta$, type II $\le\delta$, deterministic cap $B_\eta+LC^{A\setminus U}_{\mathrm{ctrl}}+\sum_{q^\star_i>0}c_i=O(m/d^2)$, matched by $\Omega(m/d^2)$
-- statement:
--   Fix a declared two-class family with $U\neq\varnothing$ in which every candidate is observable, $m=|U|$, $p,s,\tau>0$, $\delta\in(0,1/2)$.
--
--   1. The minimum defining $C^{A\setminus U}_{\mathrm{ctrl}}$ is attained. For every $d>0$ with $p+s+\tau+d<1$, every $\eta\in(0,\delta)$ and every optimizer $q^\star$, there is a tester with type-I error at most $\eta$ and type-II error at most $\delta$ under every alternative, whose declared cost on every run is at most
--   $$B_\eta+L\,C^{A\setminus U}_{\mathrm{ctrl}}+\sum_{i:\,q^\star_i>0}c_i,\qquad B_\eta=\frac1{\delta-\eta}\max_{x\in U}\Big\{H_0(\eta)\sum_{z\in U\setminus\{x\}}\bar c_z+H_1(\eta)\bar c_x\Big\}.$$
--   2. For unit boundary costs ($\bar c_x=1$ on $U$) and $\eta=\delta/2$, with $p,s,\tau,\delta$ fixed ($p+s+\tau<1$): $B_{\delta/2}\le C\,m/d^2$ for all small $d$, with $C$ independent of the topology.
--   3. For a fixed topology with unit boundary costs, the whole cap is $O(m/d^2)$.
--   4. Conversely, with unit boundary costs every $\delta$-correct tester whose declared cost is at most $K$ almost surely under the null has $K\ge m\,\mathrm{kl}(1-\delta,\delta)/K_{\mathrm{bnd}}(\tau,d)$, and hence $K\ge c\,m/d^2$ for all small $d$, with $c$ independent of the topology.
--
--   Adaptive allocation thus removes the multiplicative $\log m$ penalty even with a deterministic horizon.
--
--   Differences from the source:
--   - reading: q⋆ ("an optimizer", not specified) → the conclusion holds for every optimizer q⋆ of the cover program; reason: the stronger of the two readings (for some vs. every optimizer); every optimizer gives a valid schedule
--   - encoding: L·C_ctrl → L · Σ_i c_i q⋆_i; reason: equal, since q⋆ attains the cover program's value
--   - reading: for unit boundary costs, fixed δ, η = δ/2, this cap is O((m + log m)/d²) = O(m/d²) → B_{δ/2} ≤ C m/d² uniformly over topologies (item 2), and the total cap ≤ C m/d² for each fixed topology (item 3); reason: the term L C^{A∖U}_ctrl is not bounded by a constant times m/d² uniformly over topologies, so the uniform claim is read for B_η and the total cap with the topology fixed
--   - generalization: part (i) gives a matching Ω(m/d²) lower bound for every deterministic cap → every δ-correct tester with null-a.s. cost ≤ K has K ≥ m kl(1−δ, δ)/K_bnd(τ, d), and K ≥ c m/d² for small d, c independent of the topology; reason: a pathwise deterministic cap implies the null-a.s. hypothesis, so the Lean conclusion specializes to the source
--   - encoding: the declared two-class family (vertices low/high, candidates A, legal groups S_i with |S_i| ≥ 2, costs c_i > 0) → a TwoClassFamily structure on Fin n whose first k actions query the k groups and whose final deterministic zero-cost action represents making no query; a query of S_i reveals the coded ordered old/new outputs of its members on one fresh tape; reason: direct transcription of §10.5; the idle action carries no information and keeps the zero-query tester expressible when k = 0; coordinates outside S_i are constant
--   - encoding: declared cost, E₀[cost] → Σ_i c_i N_i with N_i = armCount i T (queries of group i before stopping), expectation a lower integral in [0, ∞]; reason: declared cost charges c_i per query of S_i
--   - encoding: δ-correct (pointwise type-II error) → IsGroupDeltaCorrect: type I ≤ δ under the simple null and type II ≤ δ under every alternative x ∈ A; reason: the paper's "type-I error and every pointwise type-II error at most δ"
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.9(vii), eqs. (80)–(82), p.21 (PDF p.23)

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

/-- **Theorem 10.9(vii), Markov truncation with a deterministic cap, eqs. (80)–(82)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem
10.9(vii), p.21 (PDF p.23)): "(vii) A deterministic declared-cost horizon can be restored without
returning to the fixed-allocation m log m penalty. Fix any η ∈ (0, δ), let H0(η) and H1(η) denote the
preceding quantities with δ replaced by η, and define Bη = 1/(δ − η) max_{x∈U} { H0(η) Σ_{z∈U\{x}} c̄z +
H1(η) c̄x }. (80) Truncating the sequential boundary block immediately before its declared cost would
exceed Bη, and then accepting that block, gives type-I error at most η, pointwise boundary type-II
error at most δ, and the deterministic total hybrid cost cap Bη + L C^{A\U}_ctrl + Σ_{i:q⋆_i>0} ci. (81)
For unit boundary costs, fixed δ, and η = δ/2, this cap is O((m + log m)/d²) = O(m/d²). (82) Part (i)
gives a matching Ω(m/d²) lower bound for every deterministic cap."

Throughout, `F` is a declared two-class family with `U ≠ ∅` (`m = |U|`) in which every candidate is
observable, `p, s, τ > 0`, and `δ ∈ (0, 1/2)`.
1. (80)–(81) The residual control-cover program has an optimizer. For every `d > 0` with
   `p + s + τ + d < 1`, every `η ∈ (0, δ)` and every optimizer `q⋆` of the
   control-cover program on `A ∖ U`, there is a tester with type-I error `≤ η` and type-II error `≤ δ` under
   every `x ∈ A`, whose declared cost is, on every run, at most `B_η + L C^{A∖U}_ctrl + Σ_{i : q⋆_i > 0} c_i`.
2. (82), uniform in the topology: for fixed `p, s, τ, δ` with `p + s + τ < 1` there are `C, d₀ > 0` such
   that `B_{δ/2} ≤ C m/d²` for every such family with unit boundary costs (`c̄_x = 1` on `U`) and every
   `d ∈ (0, d₀)`.
3. (82), the total cap for a fixed topology: with unit boundary costs and any optimizer `q⋆`, there are
   `C, d₀ > 0` with `B_{δ/2} + L C^{A∖U}_ctrl + Σ_{i : q⋆_i > 0} c_i ≤ C m/d²` for every `d ∈ (0, d₀)`.
4. The matching lower bound: with unit boundary costs, every δ-correct tester whose declared cost is
   almost surely at most `K` under the null has `K ≥ m kl(1 − δ, δ)/K_bnd(τ, d)`; and for fixed
   `p, s, τ, δ` there are `c, d₀ > 0` such that `K ≥ c m/d²` for every such family, tester and
   `d ∈ (0, d₀)`.

**Formalization Note** (82) does not say whether the total cap or `B_η` is uniformly `O(m/d²)`; the term
`L C^{A∖U}_ctrl` is not bounded by a constant times `m/d²` uniformly over topologies, so item 2 states the
uniform bound for `B_η` and item 3 the bound for the total cap with the topology fixed. "Deterministic
cap" is read as a bound holding almost surely under the null. -/
theorem theorem_10_9_vii :
    (∀ (F : TwoClassFamily) (p s τ d δ η : ℝ), 0 < p → 0 < s → 0 < τ → 0 < d →
      p + s + τ + d < 1 → 0 < δ → δ < 1 / 2 → F.unmatched.Nonempty →
      (∀ x ∈ F.A, F.Observable x) → 0 < η → η < δ →
      (∃ q : Fin F.k → ℝ, F.IsCoverOptimizer (F.A \ F.unmatched) q) ∧
      ∀ q : Fin F.k → ℝ, F.IsCoverOptimizer (F.A \ F.unmatched) q →
        ∃ (π : BanditAlgorithm.BanditPolicy (F.k + 1))
          (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
          (ψ : (ℕ → Fin (F.k + 1) × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T),
          Measurable[hT.measurableSpace] ψ ∧
          BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d none) π
              {ω | T ω < ⊤ ∧ ψ ω = true} ≤ ENNReal.ofReal η ∧
          (∀ x ∈ F.A, BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d (some x)) π
              {ω | ¬ (T ω < ⊤ ∧ ψ ω = true)} ≤ ENNReal.ofReal δ) ∧
          ∀ ω, F.declaredCost T ω ≤
            ENNReal.ofReal (F.Bcap p s τ d δ η +
              ⌈Real.log δ / Real.log (1 - d)⌉₊ * ∑ i, F.c i * q i + F.supportCost q)) ∧
    (∀ p s τ δ : ℝ, 0 < p → 0 < s → 0 < τ → p + s + τ < 1 → 0 < δ → δ < 1 / 2 →
      ∃ C d₀ : ℝ, 0 < C ∧ 0 < d₀ ∧
        ∀ F : TwoClassFamily, F.unmatched.Nonempty → (∀ x ∈ F.A, F.Observable x) →
          (∀ x ∈ F.unmatched, F.cbar x = 1) →
          ∀ d : ℝ, 0 < d → d < d₀ →
            F.Bcap p s τ d δ (δ / 2) ≤ C * F.unmatched.card / d ^ 2) ∧
    (∀ (F : TwoClassFamily) (p s τ δ : ℝ), 0 < p → 0 < s → 0 < τ →
      p + s + τ < 1 → 0 < δ → δ < 1 / 2 → F.unmatched.Nonempty →
      (∀ x ∈ F.A, F.Observable x) → (∀ x ∈ F.unmatched, F.cbar x = 1) →
      (∃ q : Fin F.k → ℝ, F.IsCoverOptimizer (F.A \ F.unmatched) q) ∧
      ∀ q : Fin F.k → ℝ, F.IsCoverOptimizer (F.A \ F.unmatched) q →
        ∃ C d₀ : ℝ, 0 < C ∧ 0 < d₀ ∧
          ∀ d : ℝ, 0 < d → d < d₀ →
            F.Bcap p s τ d δ (δ / 2) +
                ⌈Real.log δ / Real.log (1 - d)⌉₊ * ∑ i, F.c i * q i +
                F.supportCost q ≤ C * F.unmatched.card / d ^ 2) ∧
    (∀ (F : TwoClassFamily) (p s τ d δ : ℝ), 0 < p → 0 < s → 0 < τ → 0 < d →
      p + s + τ + d < 1 → 0 < δ → δ < 1 / 2 → F.unmatched.Nonempty →
      (∀ x ∈ F.A, F.Observable x) → (∀ x ∈ F.unmatched, F.cbar x = 1) →
      ∀ (π : BanditAlgorithm.BanditPolicy (F.k + 1))
        (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
        (ψ : (ℕ → Fin (F.k + 1) × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T) (K : ℝ),
        Measurable[hT.measurableSpace] ψ → F.IsGroupDeltaCorrect p s τ d δ π T ψ →
        (∀ᵐ ω ∂BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d none) π,
          F.declaredCost T ω ≤ ENNReal.ofReal K) →
        F.unmatched.card * BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ / Kbnd p s τ d ≤ K) ∧
    (∀ p s τ δ : ℝ, 0 < p → 0 < s → 0 < τ → p + s + τ < 1 → 0 < δ → δ < 1 / 2 →
      ∃ c d₀ : ℝ, 0 < c ∧ 0 < d₀ ∧ d₀ ≤ 1 - p - s - τ ∧
        ∀ F : TwoClassFamily, F.unmatched.Nonempty → (∀ x ∈ F.A, F.Observable x) →
          (∀ x ∈ F.unmatched, F.cbar x = 1) →
          ∀ d : ℝ, 0 < d → d < d₀ →
          ∀ (π : BanditAlgorithm.BanditPolicy (F.k + 1))
            (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
            (ψ : (ℕ → Fin (F.k + 1) × ℝ) → Bool)
            (hT : BanditAlgorithm.IsBanditStoppingTime T) (K : ℝ),
            Measurable[hT.measurableSpace] ψ → F.IsGroupDeltaCorrect p s τ d δ π T ψ →
            (∀ᵐ ω ∂BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d none) π,
              F.declaredCost T ω ≤ ENNReal.ofReal K) →
            c * F.unmatched.card / d ^ 2 ≤ K) := by sorry

end FairReplay.Supplement
