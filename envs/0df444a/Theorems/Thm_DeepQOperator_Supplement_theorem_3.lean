-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_3
-- name    : DeepQOperator.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:41:40.246171+00:00
-- url     : https://prove2.me/theorems/e62dd5ed-dac7-4403-9e1c-ed7a38f5203a
-- title:
--   Theorem 3, p.5 — bounded convex-box affine separation on $P_{cb}$
-- statement:
--   Consider the three-row Bellman family (6) on the convex box $P_{cb}=[-1,1]^n\times[0,1]^m$, with $m\ge2$, $r=\lceil\log_2m\rceil$, $n=2^r$ and $0<\gamma<1$.
--
--   1. All input coordinates and raw values lie in $[-1,1]$, every raw coefficient vector has $\ell_1$ norm at most one, and the three rows list $3m+n+2$ raw sites (the constant $1/4$ is listed once in row A and once in row B).
--   2. Every randomized fixed design of $N$ arbitrary affine measurements has
--   $$
--   \mathfrak h^{\mathrm{fixed,aff,ran}}_N\ \ge\ \frac{\gamma(m-N)_+}{256\pi^2m}. \tag{10}
--   $$
--   3. For every $\varepsilon>0$ put $\delta=\min\{1/2,\,32\varepsilon/\gamma\}$ and $R=2\lceil\log_2(m/\delta)\rceil+1$. There is an at-most-two-stage randomized adaptive affine algorithm, with exact real replies, whose worst-input expected regret is at most $\varepsilon$ and whose hard query budget is
--   $$
--   \min\{2m,\ 512R+2\min(m,64)\}. \tag{12}
--   $$
--   Each of its queried affine maps has coefficient $\ell_1$ norm at most one and values in $[-1,1]$ on $P_{cb}$.
--   4. For every fixed $0<\varepsilon/\gamma\le1/(512\pi^2)$, the fixed affine complexity is $\Theta(m)$ and the adaptive upper bound is $O(\log m)$.
--
--   The theorem contrasts fixed and adaptive exact affine information on a bounded convex parameter box.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: a fixed design of at most $N$ affine measurements → an `ExactDesign` with exactly $N$ rows, zero rows allowed; reason: a zero row is a known constant, so padding to $N$ rows changes nothing
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - encoding: the minimax value is at least $x$ → every algorithm of the class (measurable, on every standard Borel probability seed space) has worst regret at least $x$; reason: an infimum is at least $x$ exactly when every member is
--   - reading: fixed affine complexity is $\Theta(m)$, the adaptive upper bound is $O(\log m)$ → for each $\kappa=\varepsilon/\gamma\in(0,1/(512\pi^2)]$ there are $c,C>0$ (depending only on $\kappa$) such that for all $m\ge2$ and $\gamma$: some fixed design with at most $Cm$ rows has regret $\le\kappa\gamma$, every fixed design with regret $\le\kappa\gamma$ has at least $cm$ rows, and some adaptive algorithm with budget at most $C\log m$ has regret $\le\kappa\gamma$; reason: the base mission's reading of its Θ clause (paper.md decision 8)
--   - encoding: there are $3m+n+2$ raw sites → a listing of the raw dictionary by $3m+n+2$ indices in which only the constant site may repeat; reason: the constant $1/4$ is a site of row A and of row B; as a set the dictionary has $3m+n+1$ elements
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 3 and eqs. (10)–(12), p.5 (PDF p.8); proof in Appendix D, pp.20–22

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg

open MeasureTheory

namespace DeepQOperator.Supplement

/-- **Theorem 3 (Bounded convex-box affine separation)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy
Adaptive Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256
9f8f3285…), Theorem 3, p.5, PDF p.8; proved in Appendix D, pp.20–22).

For the family (6) on `P_cb = [-1,1]^n × [0,1]^m`, `m ≥ 2`, `0 < γ < 1`:
* all input coordinates and raw values lie in `[-1, 1]`, every raw coefficient vector has `ℓ₁`
  norm at most one, and the three rows list `3m + n + 2` raw sites (the constant `1/4` listed in
  row A and again in row B);
* every randomized fixed design of `N` arbitrary-affine measurements has worst expected regret at
  least `γ(m - N)₊/(256π²m)` (10);
* for every `ε > 0`, with `δ = min{1/2, 32ε/γ}` and `R = 2⌈log₂(m/δ)⌉ + 1` (11), an at-most-two-stage
  randomized adaptive exact affine algorithm has worst-input expected regret at most `ε` and hard
  query budget `min{2m, 512R + 2min(m, 64)}` (12), every queried map having coefficient `ℓ₁` norm at
  most one and values in `[-1, 1]` on `P_cb`;
* for every fixed `0 < ε/γ ≤ 1/(512π²)` the fixed affine complexity is `Θ(m)` and the adaptive upper
  bound is `O(log m)`.

**Formalization Note.** Fixed designs are `ExactDesign` (exactly `N` rows, zero rows allowed);
adaptive algorithms are `AdaptiveAlg` with exact replies (`IsExact`), run with fuel equal to the hard
budget. Seeds live on a standard Borel probability space; lower bounds quantify over all of them,
upper bounds choose one. `Θ`/`O` use constants `c, C > 0` depending only on `κ = ε/γ`, chosen before
`m` and `γ`; the logarithm is natural (another base changes only `C`). The "three rows" fact holds by
construction of the family. -/
theorem theorem_3 :
    (∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
      (∀ θ ∈ Pcb m, ∀ c, θ c ∈ Set.Icc (-1 : ℝ) 1) ∧
      (∀ q ∈ rawDictionary m, ∑ c, |q.1 c| ≤ 1 ∧ ∀ θ ∈ Pcb m, affEval q θ ∈ Set.Icc (-1 : ℝ) 1) ∧
      (∃ L : Fin (3 * m + nn m + 2) → AffQuery (Coord m), Set.range L = rawDictionary m ∧
        ∀ i j, L i = L j → i = j ∨ L i = constSite m) ∧
      (∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (D : ExactDesign (Coord m) Ω N), D.IsMeasurable →
        ENNReal.ofReal (γ * max 0 ((m : ℝ) - N) / (256 * Real.pi ^ 2 * m)) ≤
          designRegret (Pcb m) (loss m γ) μ D) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
          (_ : IsProbabilityMeasure μ) (A : AdaptiveAlg (Coord m) Ω),
          A.IsExact ∧ A.IsMeasurable ∧ A.IsAtMostTwoStage ∧
          (∀ ω h, A.ask ω h = true →
            ∑ c, |(A.query ω h).1 c| ≤ 1 ∧
              ∀ θ ∈ Pcb m, affEval (A.query ω h) θ ∈ Set.Icc (-1 : ℝ) 1) ∧
          algRegret (Pcb m) (loss m γ) μ A
            (min (2 * m)
              (512 * (2 * ⌈Real.logb 2 ((m : ℝ) / min (1 / 2) (32 * ε / γ))⌉₊ + 1) +
                2 * min m 64)) ≤ ENNReal.ofReal ε)) ∧
    (∀ κ : ℝ, 0 < κ → κ ≤ 1 / (512 * Real.pi ^ 2) →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
        (∃ (N : ℕ) (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (D : ExactDesign (Coord m) Ω N),
          D.IsMeasurable ∧ (N : ℝ) ≤ C * m ∧
          designRegret (Pcb m) (loss m γ) μ D ≤ ENNReal.ofReal (κ * γ)) ∧
        (∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (D : ExactDesign (Coord m) Ω N), D.IsMeasurable →
          designRegret (Pcb m) (loss m γ) μ D ≤ ENNReal.ofReal (κ * γ) → c * m ≤ N) ∧
        (∃ (N : ℕ) (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (A : AdaptiveAlg (Coord m) Ω),
          A.IsExact ∧ A.IsMeasurable ∧ (N : ℝ) ≤ C * Real.log m ∧
          algRegret (Pcb m) (loss m γ) μ A N ≤ ENNReal.ofReal (κ * γ))) := by sorry

end DeepQOperator.Supplement
