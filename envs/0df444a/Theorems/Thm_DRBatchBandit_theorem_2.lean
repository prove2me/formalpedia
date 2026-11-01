-- Prove2me | Theorems.Thm_DRBatchBandit_theorem_2
-- name    : DRBatchBandit.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:38.673364+00:00
-- url     : https://prove2.me/theorems/44fd248c-faa0-449b-b127-d3e2587e5051
-- title:
--   Theorem 2, pp.16–17 — with probability $1-\varepsilon$ the robust regret of $\hat\pi_{\mathrm{DRO}}$ is $O(\kappa^{(n)}(\Pi)/(\underline b\eta\sqrt n))$: continuous case (5) and discrete case (6)
-- statement:
--   Consider the batch contextual bandit of §2: $n$ iid draws $(X_i,Y_i(a^1),\dots,Y_i(a^d),A_i)$, of which only $(X_i,A_i,Y_i)$ with $Y_i=Y_i(A_i)$ is observed, a known logging policy $\pi_0$, a policy class $\Pi$, and a KL radius $\delta>0$. Let $\hat\pi_{\mathrm{DRO}}$ maximize the estimator $\hat Q_{\mathrm{DRO}}$ of Definition 4 over $\Pi$, and let $R_{\mathrm{DRO}}$ be the distributionally robust regret of Definition 3. Suppose Assumption 1 holds: unconfoundedness, overlap $\pi_0(a\mid x)\ge\eta>0$, and $0\le Y(a^i)\le M$. Let $\kappa^{(n)}(\Pi)$ be the entropy integral of Definition 5 and $\varepsilon>0$.
--
--   1. **Continuous case (5).** There is a universal constant $C$ such that under Assumption 2.1 (conditional densities $\ge\underline b>0$ on $[0,M]$), with probability at least $1-\varepsilon$,
--   $$R_{\mathrm{DRO}}(\hat\pi_{\mathrm{DRO}})\le\frac{4}{\underline b\eta\sqrt n}\Big(24(\sqrt2+1)\kappa^{(n)}(\Pi)+\sqrt{2\log\big(\tfrac2\varepsilon\big)}+C\Big).$$
--   2. **Discrete case (6).** Under Assumption 2.2 (rewards supported on a finite set $\mathbb D$ with $|\mathbb D|>1$ and conditional point masses $\ge\underline b>0$), when
--   $$n\ge\Big\{\frac{4}{\underline b\eta}\Big(24(\sqrt2+1)\kappa^{(n)}(\Pi)+48\sqrt{|\mathbb D|\log 2}+\sqrt{2\log\big(\tfrac2\varepsilon\big)}\Big)\Big\}^2,$$
--   with probability at least $1-\varepsilon$,
--   $$R_{\mathrm{DRO}}(\hat\pi_{\mathrm{DRO}})\le\frac{4M}{\underline b\eta\sqrt n}\Big(24(\sqrt2+1)\kappa^{(n)}(\Pi)+48\sqrt{|\mathbb D|\log 2}+\sqrt{2\log\big(\tfrac2\varepsilon\big)}\Big).$$
--
--   Neither bound depends on $\delta$; for classes with bounded $\kappa^{(n)}$ the robust regret decays at the parametric rate $n^{-1/2}$, which Theorem 3 of the paper shows is optimal up to constants.
--
--   **Formalization Note** The statement quantifies over every model, every learner returning an exact maximizer of $\hat Q_{\mathrm{DRO}}$, and every parameter, with $C$ chosen first. The failure event is bounded in (outer) measure under the law of the $n$ draws. Policies in $\Pi$ are measurable and the action-pattern sets of $\Pi$ are measurable. When no sample has $\pi(X_i)=A_i$, Lean's $0/0=0$ sets $\hat Q_{\mathrm{DRO}}(\pi)=0$; the paper leaves this event unspecified.
--
--   Differences from the source:
--   - encoding: actions a¹, …, a^d → Fin d, 0-based; rewards a vector Fin d → ℝ; reason: Lean convention; no instance changes
--   - encoding: supremum over α ≥ 0 with the α = 0 value defined by Remark 2 as ess inf → supremum over α > 0; reason: Remark 2 (p.11) defines the α = 0 value as the right limit, so the supremum is unchanged
--   - generalization: R_DRO with max over Π (an optimal policy is assumed to exist, p.10) → supremum over Π; reason: equals the maximum when it is attained; the paper says its results extend to the supremum
--   - reading: a set of n points {x₁, …, x_n} in Definition 5 → a sequence x : Fin n → X (repetitions allowed); reason: the proof applies the definition to the sample X₁, …, X_n, which may repeat
--   - reading: "with probability at least 1 − ε" (no measurability stated) → policies measurable, action-pattern sets of Π measurable, failure event bounded in outer measure; reason: the probability statement presupposes events; same convention as the published sister goal OfflinePolicyLearning.Regret.theorem3_caipwl_regret_Op
--   - encoding: ε, n unspecified → 0 < ε and 1 ≤ n; reason: log(2/ε) needs ε > 0; n is a sample size (at n = 0 Lean's 4/(bη·0) = 0)
--   - encoding: Ŵ_n = (1/(nS_n^π)) Σ W_i, undefined when S_n^π = 0 → Lean's 1/0 = 0, so Q̂_DRO(π) = 0 on that event; reason: the paper leaves the event unspecified; in case (5) its probability is covered by the bound since b·M ≤ 1, and in case (6) the threshold on n excludes it on the good event
--   - encoding: κ⁽ⁿ⁾(Π) a real number → (entropyIntegralN n Pol).toReal; reason: κ⁽ⁿ⁾ is finite since N_H⁽ⁿ⁾ ≤ dⁿ, so toReal is its value
--   - encoding: Y(aⁱ)|X has a conditional density fᵢ(yᵢ|x) ≥ b > 0 on [0, M] (Assumption 2.1) → the law of y i under M.κY x is ≪ Lebesgue and b·λ(s) ≤ its mass of s for every measurable s ⊆ [0, M] (DensityLB); reason: equivalent by the Radon–Nikodym theorem (a density ≥ b a.e. on [0, M] can be chosen ≥ b everywhere there)
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, Theorem 2, pp.16–17 (equations (5) and (6)); Assumptions 1–2, pp.8–9; Definitions 2–5, pp.10–16; (4), p.15. PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_DRBatchBandit_RobustValue
import Definitions.Def_DRBatchBandit_Assumptions
import Definitions.Def_DRBatchBandit_Estimator
import Definitions.Def_DRBatchBandit_EntropyIntegral

open MeasureTheory ProbabilityTheory

universe u

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

/-- Theorem 2 (Si, Zhang, Zhou & Blanchet, *Distributionally Robust Batch Contextual Bandits*,
arXiv:2006.05630v7, pp.16–17). Suppose Assumption 1 is enforced. Then, with probability at least
`1 − ε`:

* (5) under Assumption 2.1,
  `R_DRO(π̂_DRO) ≤ 4/(bη√n) (24(√2 + 1)κ⁽ⁿ⁾(Π) + √(2 log(2/ε)) + C)`, where `C` is a universal
  constant;
* (6) under Assumption 2.2, when
  `n ≥ {4/(bη) (24(√2 + 1)κ⁽ⁿ⁾(Π) + 48√(|𝔻| log 2) + √(2 log(2/ε)))}²`,
  `R_DRO(π̂_DRO) ≤ 4M/(bη√n) (24(√2 + 1)κ⁽ⁿ⁾(Π) + 48√(|𝔻| log 2) + √(2 log(2/ε)))`.

**Formalization Note.**
* Actions are `Fin d`; a draw is `Draw X d = X × ((Fin d → ℝ) × Fin d)`; `π₀(a|x)` is `M.e x a`;
  the `n` iid draws have law `M.sample n`, and `π̂_DRO` sees only the observed triples
  `obs (D i)`. Assumption 1.1 is built into `M.law`; 1.2 is `Overlap M η`; 1.3 is
  `BoundedReward M Mrew` (`Mrew` is the paper's `M`); 2.1 is `DensityLB M Mrew b`; 2.2 is
  `PointMassLB M 𝔻 b`.
* `π̂_DRO` is any learner returning a maximizer of `Q̂_DRO` over `Π` (`IsDROLearner`); `Q̂_DRO`
  and the duals are suprema over `α > 0` (Remark 2); `R_DRO` uses the supremum over `Π`.
* `κ⁽ⁿ⁾(Π)` is `(entropyIntegralN n Pol).toReal` (finite, as `N_H⁽ⁿ⁾ ≤ dⁿ`), with `n`-point
  sequences for the point sets of Definition 5.
* Policies are measurable and the action-pattern sets of `Π` are measurable
  (`MeasurablePolicyClass`); the failure event is bounded in outer measure.
* `n ≥ 1` and `ε > 0`. `C` is chosen before every type, model and parameter.
* If no sample has `π(Xᵢ) = Aᵢ`, Lean's `0/0 = 0` makes `Q̂_DRO(π) = 0`; the paper is silent on
  this event. -/
theorem theorem_2 :
    (∃ C : ℝ, ∀ {X : Type u} [MeasurableSpace X] {d : ℕ} (M : Model X d)
      (Mrew η b δ ε : ℝ) (n : ℕ) (Pol : Set (X → Fin d))
      (πhat : (Fin n → Obs X d) → X → Fin d),
      0 < δ → 0 < ε → 1 ≤ n →
      Overlap M η → BoundedReward M Mrew → DensityLB M Mrew b →
      MeasurablePolicyClass Pol → IsDROLearner M δ Pol πhat →
      M.sample n {D | 4 / (b * η * Real.sqrt n) *
          (24 * (Real.sqrt 2 + 1) * (entropyIntegralN n Pol).toReal +
            Real.sqrt (2 * Real.log (2 / ε)) + C) <
          RDRO M δ Pol (πhat fun i => obs (D i))} ≤ ENNReal.ofReal ε) ∧
    (∀ {X : Type u} [MeasurableSpace X] {d : ℕ} (M : Model X d)
      (Mrew η b δ ε : ℝ) (n : ℕ) (Pol : Set (X → Fin d))
      (πhat : (Fin n → Obs X d) → X → Fin d) (𝔻 : Finset ℝ),
      0 < δ → 0 < ε → 1 ≤ n →
      Overlap M η → BoundedReward M Mrew → PointMassLB M 𝔻 b →
      MeasurablePolicyClass Pol → IsDROLearner M δ Pol πhat →
      (4 / (b * η) * (24 * (Real.sqrt 2 + 1) * (entropyIntegralN n Pol).toReal +
          48 * Real.sqrt (𝔻.card * Real.log 2) + Real.sqrt (2 * Real.log (2 / ε)))) ^ 2 ≤ n →
      M.sample n {D | 4 * Mrew / (b * η * Real.sqrt n) *
          (24 * (Real.sqrt 2 + 1) * (entropyIntegralN n Pol).toReal +
            48 * Real.sqrt (𝔻.card * Real.log 2) + Real.sqrt (2 * Real.log (2 / ε))) <
          RDRO M δ Pol (πhat fun i => obs (D i))} ≤ ENNReal.ofReal ε) := by sorry

end DRBatchBandit
