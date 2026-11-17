-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_7
-- name    : DeepQOperator.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:43:55.280373+00:00
-- url     : https://prove2.me/theorems/a97d947c-1702-4877-a712-a2789eadad4c
-- title:
--   Theorem 7, p.13 — finite-reply separation for the envelope family
-- statement:
--   Consider the envelope family (13)–(14) with $m\ge2$ and $0<\gamma<1$, in the scalar-reply model of Appendix A. Each field is one affine scalar quantized to a symbol of $b\ge1$ bits, and the hard reply budget $B$ bounds the total bits on every input and random path.
--
--   1. For integers $0\le B\le m$, every fixed affine protocol with hard budget $B$ satisfies
--   $$
--   \mathfrak E^{\mathrm{fixed,aff,bit}}_B\ \ge\ \frac{\gamma(m+1-B)}{32\pi^2(\sqrt m+1)^2}. \tag{27}
--   $$
--   2. Every adaptive raw protocol with hard reply budget $B\ge0$ satisfies
--   $$
--   \mathfrak E^{\mathrm{adaptive,raw,bit}}_B\ \ge\ \frac\gamma4\Big[1-\frac{2^B-1}{m}\Big]_+. \tag{28}
--   $$
--   3. For $0<\tau\le1/4$ let
--   $$
--   b_s(\tau)=\Big\lceil\log_2\Big(1+\Big\lceil\frac{m+1}{\tau}\Big\rceil\Big)\Big\rceil,\qquad b_z(\tau)=\Big\lceil\log_2\Big(1+\Big\lceil\frac1{2\tau}\Big\rceil\Big)\Big\rceil. \tag{29}
--   $$
--   There is an adaptive raw scheme with at most three replies and $b_s+2b_z$ reply bits, and a fixed raw scheme with $b_s+mb_z$ reply bits. Each has worst expected regret at most $\gamma\tau$.
--   4. Consequently, for every fixed $0<\varepsilon/\gamma\le1/4096$,
--   $$
--   C_{\mathrm{fix}}(\varepsilon)=\Theta(m),\qquad C_{\mathrm{ad}}(\varepsilon)=\Theta(\log(m+1)), \tag{30}
--   $$
--   where $C_{\mathrm{fix}}$ and $C_{\mathrm{ad}}$ are the least budgets of fixed affine, resp. adaptive raw, protocols with worst expected regret at most $\varepsilon$. The constants depend only on the tolerance ratio.
--
--   The theorem converts the exact-query separation into a reply-bit separation: linear in $m$ for fixed protocols, logarithmic for adaptive ones.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - encoding: the minimax value is at least $x$ → every algorithm of the class (measurable, on every standard Borel probability seed space) has worst regret at least $x$; reason: an infimum is at least $x$ exactly when every member is
--   - encoding: a reply of $b\in\mathbb N_0$ bits; zero-bit replies → the published `ReplyProtocol`: every asked field has length $\ge1$ and symbol below $2^{\text{len}}$; reason: a zero-bit reply is constant and can be removed (App. A, p.13)
--   - encoding: $\lceil\log_2 x\rceil$ of an integer $x\ge1$ → `Nat.clog 2 x`; reason: equal for integers $x\ge1$
--   - reading: $C_{\mathrm{fix}}(\varepsilon)=\Theta(m)$, $C_{\mathrm{ad}}(\varepsilon)=\Theta(\log(m+1))$ → for each $\kappa\in(0,1/4096]$ there are $c,C>0$ such that for all $m\ge2$, $\gamma$: a fixed (raw) protocol with budget $\le Cm$ and regret $\le\kappa\gamma$ exists and every fixed protocol with regret $\le\kappa\gamma$ has budget $\ge cm$; an adaptive raw protocol with budget $\le C\log(m+1)$ exists and every adaptive raw protocol with regret $\le\kappa\gamma$ has budget $\ge c\log(m+1)$; reason: a least budget is described by an attaining protocol and a lower bound on all protocols; constants depend only on the tolerance ratio, as the theorem says
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 7 and eqs. (27)–(30), p.13 (PDF p.16); reply model of Appendix A, p.13; proof in Appendix C, pp.17–19

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ReplyProtocol
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
import Definitions.Def_DeepQOperator_Supplement_Envelope

open MeasureTheory

namespace DeepQOperator.Supplement

/-- **Theorem 7 (Finite-reply separation)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive
Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256 9f8f3285…),
Theorem 7, p.13, PDF p.16; proved in Appendix C, pp.17–19).

For the envelope family (13), `m ≥ 2`, `0 < γ < 1`, in the scalar-reply model of Appendix A:
* for integers `0 ≤ B ≤ m`, every fixed affine protocol with hard budget `B` has worst expected
  regret at least `γ(m+1-B)/(32π²(√m+1)²)` (27);
* every adaptive raw protocol with hard reply budget `B ≥ 0` has worst expected regret at least
  `(γ/4)[1 - (2^B - 1)/m]₊` (28);
* for `0 < τ ≤ 1/4`, with `b_s(τ) = ⌈log₂(1 + ⌈(m+1)/τ⌉)⌉` and `b_z(τ) = ⌈log₂(1 + ⌈1/(2τ)⌉)⌉` (29), an
  adaptive raw scheme with at most three replies and `b_s + 2b_z` reply bits and a fixed raw scheme
  with `b_s + m b_z` reply bits each have worst expected regret at most `γτ`;
* for every fixed `0 < ε/γ ≤ 1/4096`, `C_fix(ε) = Θ(m)` and `C_ad(ε) = Θ(log(m+1))` (30), where `C_fix`
  is the least hard budget of a fixed affine protocol and `C_ad` that of an adaptive raw protocol with
  worst expected regret at most `ε`.

**Formalization Note.** Protocols are the published `ReplyProtocol` (lengths `≥ 1`, symbols below
`2^len`, quantizers measurable functions of the field's scalar, the seed and earlier symbols) on a
standard Borel probability seed space; "fixed" is `IsFixed`, "raw" is `IsRawProtocol (envDictionary m)`,
the budget `HardBudgetOn (envBox m) B` holds on every input and seed. `⌈log₂ x⌉` for an integer
`x ≥ 1` is `Nat.clog 2 x`. `Θ` is read with constants `c, C > 0` depending only on `κ = ε/γ`, chosen
before `m` and `γ`; the least-budget statements are stated as an attaining protocol plus a lower bound
on every protocol (no `sInf` on `ℕ`). The logarithm is natural. -/
theorem theorem_7 :
    (∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
      (∀ B : ℕ, B ≤ m → ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (P : ReplyProtocol (EnvCoord m) Ω),
        P.IsMeasurable → P.IsFixed → P.HardBudgetOn (envBox m) B →
        ENNReal.ofReal (γ * ((m : ℝ) + 1 - B) / (32 * Real.pi ^ 2 * (Real.sqrt m + 1) ^ 2)) ≤
          replyRegret (envBox m) (envLoss m γ 0) μ P B) ∧
      (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (P : ReplyProtocol (EnvCoord m) Ω),
        P.IsMeasurable → IsRawProtocol (envDictionary m) P → P.HardBudgetOn (envBox m) B →
        ENNReal.ofReal (γ / 4 * max 0 (1 - ((2 : ℝ) ^ B - 1) / m)) ≤
          replyRegret (envBox m) (envLoss m γ 0) μ P B) ∧
      (∀ τ : ℝ, 0 < τ → τ ≤ 1 / 4 →
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (P : ReplyProtocol (EnvCoord m) Ω),
          P.IsMeasurable ∧ IsRawProtocol (envDictionary m) P ∧ AtMostFields P (envBox m) 3 ∧
          P.HardBudgetOn (envBox m)
            (Nat.clog 2 (1 + ⌈((m : ℝ) + 1) / τ⌉₊) + 2 * Nat.clog 2 (1 + ⌈1 / (2 * τ)⌉₊)) ∧
          replyRegret (envBox m) (envLoss m γ 0) μ P
              (Nat.clog 2 (1 + ⌈((m : ℝ) + 1) / τ⌉₊) + 2 * Nat.clog 2 (1 + ⌈1 / (2 * τ)⌉₊)) ≤
            ENNReal.ofReal (γ * τ)) ∧
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (P : ReplyProtocol (EnvCoord m) Ω),
          P.IsMeasurable ∧ IsRawProtocol (envDictionary m) P ∧ P.IsFixed ∧
          P.HardBudgetOn (envBox m)
            (Nat.clog 2 (1 + ⌈((m : ℝ) + 1) / τ⌉₊) + m * Nat.clog 2 (1 + ⌈1 / (2 * τ)⌉₊)) ∧
          replyRegret (envBox m) (envLoss m γ 0) μ P
              (Nat.clog 2 (1 + ⌈((m : ℝ) + 1) / τ⌉₊) + m * Nat.clog 2 (1 + ⌈1 / (2 * τ)⌉₊)) ≤
            ENNReal.ofReal (γ * τ)))) ∧
    (∀ κ : ℝ, 0 < κ → κ ≤ 1 / 4096 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (P : ReplyProtocol (EnvCoord m) Ω) (B : ℕ),
          P.IsMeasurable ∧ IsRawProtocol (envDictionary m) P ∧ P.IsFixed ∧
          P.HardBudgetOn (envBox m) B ∧ (B : ℝ) ≤ C * m ∧
          replyRegret (envBox m) (envLoss m γ 0) μ P B ≤ ENNReal.ofReal (κ * γ)) ∧
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (P : ReplyProtocol (EnvCoord m) Ω),
          P.IsMeasurable → P.IsFixed → P.HardBudgetOn (envBox m) B →
          replyRegret (envBox m) (envLoss m γ 0) μ P B ≤ ENNReal.ofReal (κ * γ) → c * m ≤ B) ∧
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (P : ReplyProtocol (EnvCoord m) Ω) (B : ℕ),
          P.IsMeasurable ∧ IsRawProtocol (envDictionary m) P ∧
          P.HardBudgetOn (envBox m) B ∧ (B : ℝ) ≤ C * Real.log (m + 1) ∧
          replyRegret (envBox m) (envLoss m γ 0) μ P B ≤ ENNReal.ofReal (κ * γ)) ∧
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (P : ReplyProtocol (EnvCoord m) Ω),
          P.IsMeasurable → IsRawProtocol (envDictionary m) P → P.HardBudgetOn (envBox m) B →
          replyRegret (envBox m) (envLoss m γ 0) μ P B ≤ ENNReal.ofReal (κ * γ) →
          c * Real.log (m + 1) ≤ B)) := by sorry

end DeepQOperator.Supplement
