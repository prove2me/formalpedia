-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_9_iii
-- name    : FairReplay.Supplement.theorem_10_9_iii
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:00:35.299867+00:00
-- url     : https://prove2.me/theorems/8ea14ee9-3ff2-45a9-bdc0-d965462c71bc
-- title:
--   Theorem 10.9(iii) — $K_{\mathrm{ctrl}}=d+O(d^2)$, $K_{\mathrm{bnd}}=\frac{d^2}2(\frac1\tau+\frac1r)+O(d^3)$; $\Theta(d^{-1})$ with controls, $\Omega(d^{-2})$ without
-- statement:
--   Fix $p,s,\tau>0$ with $p+s+\tau<1$, $r=1-p-s-\tau$, $\delta\in(0,1/2)$, $a=\mathrm{kl}(1-\delta,\delta)$, and let $d\to0^+$.
--
--   1. $K_{\mathrm{ctrl}}(d)=d+O(d^2)$ and $K_{\mathrm{bnd}}(\tau,d)=\frac{d^2}{2}\big(\frac1\tau+\frac1r\big)+O(d^3)$.
--   2. If the family has a candidate and $C_{\mathrm{ctrl}}<\infty$: the control-cover minimum is attained, the lower program of (i) is finite and $d\,Q_{\mathrm{LB}}(d)\to a\,C_{\mathrm{ctrl}}$; the upper construction of (ii) satisfies $d\,\big(L C_{\mathrm{ctrl}}+\sum_{q^\star_i>0}c_i\big)\to\log(1/\delta)\,C_{\mathrm{ctrl}}$, the same control-cover geometry; and the optimal expected null declared cost is $\Theta(d^{-1}\log(1/\delta))$.
--   3. If some observable candidate has no control-compatible legal group, every $\delta$-correct tester has expected null declared cost at least $c\,d^{-2}\log(1/\delta)$ for all small $d$, for a constant $c>0$.
--   4. If some candidate lies in no legal group, no $\delta$-correct tester exists.
--
--   Differences from the source:
--   - encoding: O(d²), O(d³) as d → 0 → Asymptotics.IsBigO along 𝓝[>] 0; reason: standard
--   - reading: matching leading control-cover geometry and Θ(d⁻¹ log(1/δ)) order, if C_ctrl < ∞ → d·QLB(d) → a·C_ctrl, d·(L C_ctrl + Σ_{q⋆_i>0} c_i) → log(1/δ)·C_ctrl, and c log(1/δ)/d ≤ Q⋆₀(d) ≤ C log(1/δ)/d for small d; reason: the leading coefficients of the lower program and the upper construction are both multiples of C_ctrl; Θ is read on the optimal cost Q⋆₀, which both sandwich
--   - reading: the declared family (alternatives raise a high candidate) → A ≠ ∅ assumed in item 2; reason: the family presupposes a candidate; with A = ∅ (C_ctrl = 0) the tester that stops at once and accepts is δ-correct with cost 0, so no Θ(d⁻¹) lower bound holds
--   - encoding: every tester requires Ω(d⁻² log(1/δ)) expected declared cost → ∃ c, d₀ > 0: E₀[cost] ≥ c log(1/δ)/d² for every δ-correct tester and d ∈ (0, d₀); reason: Ω with constants chosen before d
--   - generalization: no finite-cost δ-correct tester exists → no δ-correct tester exists; reason: implies the paper's claim
--   - encoding: the declared two-class family (vertices low/high, candidates A, legal groups S_i with |S_i| ≥ 2, costs c_i > 0) → a TwoClassFamily structure on Fin n whose first k actions query the k groups and whose final deterministic zero-cost action represents making no query; a query of S_i reveals the coded ordered old/new outputs of its members on one fresh tape; reason: direct transcription of §10.5; the idle action carries no information and keeps the zero-query tester expressible when k = 0; coordinates outside S_i are constant
--   - encoding: declared cost, E₀[cost] → Σ_i c_i N_i with N_i = armCount i T (queries of group i before stopping), expectation a lower integral in [0, ∞]; reason: declared cost charges c_i per query of S_i
--   - encoding: δ-correct (pointwise type-II error) → IsGroupDeltaCorrect: type I ≤ δ under the simple null and type II ≤ δ under every alternative x ∈ A; reason: the paper's "type-I error and every pointwise type-II error at most δ"
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.9(iii), eq. (68), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_armCount
import Definitions.Def_FairReplay_Supplement_TwoClassFamily
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_coverLP
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_QLB
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_Qstar0

open MeasureTheory Filter Topology Asymptotics

namespace FairReplay.Supplement

open TwoClassFamily

/-- **Theorem 10.9(iii), expansions and regimes, eq. (68)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.9(iii), p.19 (PDF p.21)):
"(iii) For fixed p, s, τ > 0 with p + s + τ < 1, Kctrl(d) = d + O(d²), Kbnd(τ, d) = d²/2 (1/τ + 1/r) + O(d³).
(68) Consequently, if Cctrl < ∞, the lower program and upper construction have matching leading
control-cover geometry and Θ(d−1 log(1/δ)) fixed-confidence order, up to rounding and standard
constant factors. If some observable high candidate has no control-compatible legal group, then
every tester requires Ω(d−2 log(1/δ)) expected declared cost at fixed τ > 0. If a candidate is
completely unobservable, no finite-cost δ-correct tester exists."

With `r = 1 − p − s − τ`, `a = kl(1 − δ, δ)`, `L(d) = ⌈log δ / log(1 − d)⌉`, the family `F` and `p, s, τ, δ` fixed
and `d → 0⁺`:
1. (68) `K_ctrl(d) − d = O(d²)` and `K_bnd(τ, d) − (d²/2)(1/τ + 1/r) = O(d³)`;
2. if `A ≠ ∅` and `C_ctrl < ∞`: the cover program has an optimizer, the lower program is finite,
   `d · QLB(d) → a C_ctrl`; for every optimizer
   `q⋆` the upper construction (67) satisfies `d · (L(d) C_ctrl + Σ_{q⋆_i>0} c_i) → log(1/δ) C_ctrl`; and the
   optimal expected null declared cost satisfies `c log(1/δ)/d ≤ Q⋆₀(d) ≤ C log(1/δ)/d` for small `d`;
3. if some observable candidate `x ∈ A` has no control group, there are `c, d₀ > 0` such that every
   δ-correct tester has `E₀[cost] ≥ c log(1/δ)/d²` for `d ∈ (0, d₀)`;
4. if some candidate lies in no legal group, no δ-correct tester exists (for any `d`).

**Formalization Note** `O(·)` is `Asymptotics.IsBigO` along `d → 0⁺`. `A ≠ ∅` is added in item 2: with
`A = ∅` the problem has no alternative and the `Θ(1/d)` claim fails. Item 4 asserts that no δ-correct
tester exists at all, which implies the paper's "no finite-cost δ-correct tester". -/
theorem theorem_10_9_iii :
    (∀ p s τ : ℝ, 0 < p → 0 < s → 0 < τ → p + s + τ < 1 →
      (fun d => Kctrl p s τ d - d) =O[𝓝[>] 0] (fun d => d ^ 2) ∧
      (fun d => Kbnd p s τ d - d ^ 2 / 2 * (1 / τ + 1 / (1 - p - s - τ))) =O[𝓝[>] 0]
        (fun d => d ^ 3)) ∧
    (∀ (F : TwoClassFamily) (p s τ δ : ℝ), 0 < p → 0 < s → 0 < τ → p + s + τ < 1 → 0 < δ →
      δ < 1 / 2 → F.A.Nonempty → F.Cctrl < ⊤ →
      (∀ d, 0 < d → d < 1 - p - s - τ → F.QLB p s τ d δ ≠ ⊤) ∧
      Tendsto (fun d => d * (F.QLB p s τ d δ).toReal) (𝓝[>] 0)
        (𝓝 (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ * F.Cctrl.toReal)) ∧
      (∃ q : Fin F.k → ℝ, F.IsCoverOptimizer F.A q) ∧
      (∀ q, F.IsCoverOptimizer F.A q →
        Tendsto (fun d => d * (⌈Real.log δ / Real.log (1 - d)⌉₊ * F.Cctrl.toReal + F.supportCost q))
          (𝓝[>] 0) (𝓝 (Real.log (1 / δ) * F.Cctrl.toReal))) ∧
      ∃ c C d₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < d₀ ∧ d₀ ≤ 1 - p - s - τ ∧
        ∀ d, 0 < d → d < d₀ →
          ENNReal.ofReal (c * Real.log (1 / δ) / d) ≤ F.Qstar0 p s τ d δ ∧
          F.Qstar0 p s τ d δ ≤ ENNReal.ofReal (C * Real.log (1 / δ) / d)) ∧
    (∀ (F : TwoClassFamily) (p s τ δ : ℝ), 0 < p → 0 < s → 0 < τ → p + s + τ < 1 → 0 < δ →
      δ < 1 / 2 → (∃ x ∈ F.A, F.Observable x ∧ ∀ i, ¬ F.IsControl x i) →
      ∃ c d₀ : ℝ, 0 < c ∧ 0 < d₀ ∧ d₀ ≤ 1 - p - s - τ ∧
        ∀ d, 0 < d → d < d₀ →
          ∀ (π : BanditAlgorithm.BanditPolicy (F.k + 1))
            (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
            (ψ : (ℕ → Fin (F.k + 1) × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T),
            Measurable[hT.measurableSpace] ψ → F.IsGroupDeltaCorrect p s τ d δ π T ψ →
            ENNReal.ofReal (c * Real.log (1 / δ) / d ^ 2) ≤
              ∫⁻ ω, F.declaredCost T ω
                ∂BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d none) π) ∧
    (∀ (F : TwoClassFamily) (p s τ d δ : ℝ), 0 < p → 0 < s → 0 < τ → 0 < d →
      p + s + τ + d < 1 → 0 < δ → δ < 1 / 2 → (∃ x ∈ F.A, ¬ F.Observable x) →
      ¬ ∃ (π : BanditAlgorithm.BanditPolicy (F.k + 1))
          (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
          (ψ : (ℕ → Fin (F.k + 1) × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T),
          Measurable[hT.measurableSpace] ψ ∧ F.IsGroupDeltaCorrect p s τ d δ π T ψ) := by sorry

end FairReplay.Supplement
