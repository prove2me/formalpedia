-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_15
-- name    : DeepQOperator.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:47:35.860775+00:00
-- url     : https://prove2.me/theorems/f4091753-822e-42de-a471-bafa64fd16a4
-- title:
--   Theorem 15, p.46 — complete bounded-error adaptive curves for the normalized family
-- statement:
--   For the normalized family (76)–(78), $m\ge2$, $0<\gamma<1$, $c=\gamma/m$, and every known error level $\tau\ge0$: each queried raw site $q$ returns $q(\theta)+e$ with $|e|\le\tau$. The error is chosen by a causal rule from the parameter, the current query and the public preceding transcript. Rule and parameter are fixed before the algorithm's private randomness. Then
--   $$
--   \mathfrak B^{\det}_N(\tau)=\begin{cases}c/2,&N=0,1,\\c\min\{2\tau,1/2\},&N\ge2,\end{cases}\qquad \mathfrak B^{\mathrm{ran}}_N(\tau)=\begin{cases}c/4,&N=0,1,\\c\min\{\tau,1/4\},&N\ge2.\end{cases} \tag{82}
--   $$
--   The two-query upper bounds require no promise that the address or the contrast is separated from a boundary. The lower bounds for $N\ge2$ hold for every finite budget, even against randomized acquisition, using one fixed corrupted response for each raw site: there are two parameters in $P_m$ and one reply per raw site, within $\tau$ of both parameters' values, against which every algorithm with any budget has the stated worst loss.
--
--   The curves show that adaptive exactness degrades linearly in the observation error and that repetition cannot help.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - encoding: the minimax value is at least $x$ → every algorithm of the class (measurable, on every standard Borel probability seed space) has worst regret at least $x$; reason: an infimum is at least $x$ exactly when every member is
--   - reading: the minimax value is at most $x$ (an upper bound on an infimum) → there is an algorithm of the class whose worst regret is at most $x$; reason: the source proves each upper bound by an explicit algorithm or design it describes
--   - encoding: error rule chosen with the parameter before the seed, depending on the parameter, the current query and the public preceding transcript → a supremum over $\theta\in P_m$ and over functions $E(h,q)$ with $|E|\le\tau$ of (public transcript, current query); the seed is not an argument; reason: dependence on the parameter is the supremum over $\theta$ outside $E$
--   - encoding: one fixed corrupted response for each raw site → $\exists\theta_1,\theta_2\in P_m$ and $y$ on queries with $|y(q)-q(\theta_i)|\le\tau$ on raw sites, such that every algorithm, for every budget, has worst (expected) loss over $\{\theta_1,\theta_2\}$ at least the $N\ge2$ value when every query is answered by $y$; reason: the witness the sentence describes; it is stated for every budget $N$, as in 'every finite budget'
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 15 and eq. (82), p.46 (PDF p.49); error model §L.3, p.45 (PDF p.48); proof in Appendix Q

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
import Definitions.Def_DeepQOperator_Supplement_Normalized

open MeasureTheory

namespace DeepQOperator.Supplement

/-- **Theorem 15 (Complete bounded-error adaptive curves)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy
Adaptive Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256
9f8f3285…), Theorem 15, p.46, PDF p.49; model §L.3 p.45, proof Appendix Q pp.64–65).

For the raw normalized family (76)–(78), `m ≥ 2`, `0 < γ < 1`, `c = γ/m`, and every `τ ≥ 0`, when each
queried raw site `q` returns `q(θ) + e` with `|e| ≤ τ` and `e` chosen by a causal error rule:
`𝔅^det_N(τ) = c/2` for `N = 0, 1` and `c·min{2τ, 1/2}` for `N ≥ 2`, and `𝔅^ran_N(τ) = c/4` for
`N = 0, 1` and `c·min{τ, 1/4}` for `N ≥ 2` (82). The two-query upper bounds hold on all of `P_m`, with
no promise that the address or the contrast is separated from a boundary. The lower bounds for
`N ≥ 2` hold for every finite budget, even against randomized acquisition, using one fixed corrupted
response for each raw site.

**Formalization Note.** Algorithms are `AdaptiveAlg (NCoord m) Ω` with exact observation maps
(`IsExact`: the algorithm sees the corrupted reply itself) and raw queries, run with fuel `N`.
`noisyRegret` takes the supremum over `θ ∈ P_m` and over error rules `E` with `|E| ≤ τ`; `E` sees the
public preceding transcript (queries and replies) and the current query, is chosen with `θ` before the
seed, and cannot see the seed; the final decision may use fresh coins from the seed. Deterministic
algorithms have seed `Unit` (Dirac measure) and carry no measurability condition; randomized ones are
measurable on a standard Borel probability space. Each value is stated as a lower bound for the class
and an algorithm attaining it. The last clause states the lower-bound witness: two parameters
`θ₁, θ₂ ∈ P_m` and one reply `y q` for each raw site `q`, within `τ` of both `q(θ₁)` and `q(θ₂)`, against
which every algorithm, for every budget `N`, has the stated worst loss over `{θ₁, θ₂}`. -/
theorem theorem_15 :
    ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ τ : ℝ, 0 ≤ τ →
      -- deterministic curve
      (∀ N : ℕ, N ≤ 1 →
        (∀ A : AdaptiveAlg (NCoord m) Unit, A.IsExact → A.IsRaw (nDictionary m) →
          ENNReal.ofReal (γ / m / 2) ≤
            noisyRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A N τ) ∧
        (∃ A : AdaptiveAlg (NCoord m) Unit, A.IsExact ∧ A.IsRaw (nDictionary m) ∧
          noisyRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A N τ ≤
            ENNReal.ofReal (γ / m / 2))) ∧
      (∀ N : ℕ, 2 ≤ N →
        (∀ A : AdaptiveAlg (NCoord m) Unit, A.IsExact → A.IsRaw (nDictionary m) →
          ENNReal.ofReal (γ / m * min (2 * τ) (1 / 2)) ≤
            noisyRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A N τ) ∧
        (∃ A : AdaptiveAlg (NCoord m) Unit, A.IsExact ∧ A.IsRaw (nDictionary m) ∧
          noisyRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A N τ ≤
            ENNReal.ofReal (γ / m * min (2 * τ) (1 / 2)))) ∧
      -- randomized curve
      (∀ N : ℕ, N ≤ 1 →
        (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (A : AdaptiveAlg (NCoord m) Ω),
          A.IsExact → A.IsRaw (nDictionary m) → A.IsMeasurable →
          ENNReal.ofReal (γ / m / 4) ≤ noisyRegret (nBox m) (nLoss m γ) μ A N τ) ∧
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (A : AdaptiveAlg (NCoord m) Ω),
          A.IsExact ∧ A.IsRaw (nDictionary m) ∧ A.IsMeasurable ∧
          noisyRegret (nBox m) (nLoss m γ) μ A N τ ≤ ENNReal.ofReal (γ / m / 4))) ∧
      (∀ N : ℕ, 2 ≤ N →
        (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (A : AdaptiveAlg (NCoord m) Ω),
          A.IsExact → A.IsRaw (nDictionary m) → A.IsMeasurable →
          ENNReal.ofReal (γ / m * min τ (1 / 4)) ≤ noisyRegret (nBox m) (nLoss m γ) μ A N τ) ∧
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (A : AdaptiveAlg (NCoord m) Ω),
          A.IsExact ∧ A.IsRaw (nDictionary m) ∧ A.IsMeasurable ∧
          noisyRegret (nBox m) (nLoss m γ) μ A N τ ≤ ENNReal.ofReal (γ / m * min τ (1 / 4)))) ∧
      -- the lower bounds for `N ≥ 2` use one fixed corrupted response for each raw site
      (∃ θ₁ ∈ nBox m, ∃ θ₂ ∈ nBox m, ∃ y : AffQuery (NCoord m) → ℝ,
        (∀ q ∈ nDictionary m, |y q - affEval q θ₁| ≤ τ ∧ |y q - affEval q θ₂| ≤ τ) ∧
        (∀ (N : ℕ) (A : AdaptiveAlg (NCoord m) Unit), A.IsExact → A.IsRaw (nDictionary m) →
          γ / m * min (2 * τ) (1 / 2) ≤
            max (nLoss m γ (A.decisionWith (fun _ q => y q) N ()) θ₁)
              (nLoss m γ (A.decisionWith (fun _ q => y q) N ()) θ₂)) ∧
        (∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (A : AdaptiveAlg (NCoord m) Ω),
          A.IsExact → A.IsRaw (nDictionary m) → A.IsMeasurable →
          ENNReal.ofReal (γ / m * min τ (1 / 4)) ≤
            max (∫⁻ ω, ENNReal.ofReal (nLoss m γ (A.decisionWith (fun _ q => y q) N ω) θ₁) ∂μ)
              (∫⁻ ω, ENNReal.ofReal (nLoss m γ (A.decisionWith (fun _ q => y q) N ω) θ₂) ∂μ))) := by sorry

end DeepQOperator.Supplement
