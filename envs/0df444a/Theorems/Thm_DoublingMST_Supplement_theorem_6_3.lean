-- Prove2me | Theorems.Thm_DoublingMST_Supplement_theorem_6_3
-- name    : DoublingMST.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:19:43.560932+00:00
-- url     : https://prove2.me/theorems/2e944af4-a668-439d-9b5b-e3674d21fac6
-- title:
--   Theorem 6.3 — $b$-ary comparison lower bound $n\log_b n-O(n\log_b(2\alpha))$ for an explicit $\alpha$-approximate MST on the line
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every $n\ge2$, every integer $b\ge2$ and every factor $\alpha\ge1$. Let $(A_\omega)_{\omega\in\Omega}$ be a randomized $b$-ary comparison algorithm over a probability space $(\Omega,\mu)$, and for an input $x$ (distinct positions $x_0,\dots,x_{n-1}\in\mathbb R$ of the labelled points, with metric $d_x(u,v)=|x_u-x_v|$) call a run successful if it outputs an explicit spanning tree $T$ with $w_{d_x}(T)\le\alpha\,\mathrm{MST}(d_x)$. Write $c$ for the number of comparisons.
--
--   1. (Deterministic or Las Vegas.) If every run on every input is successful with probability $1$, then some input $x$ has
--   $$\mathbb E[c]\ \ge\ n\log_b n-C\,n\log_b(2\alpha).$$
--   2. (Bounded error.) If on every input the success probability is at least $2/3$, then some input $x$ has
--   $$\mathbb E[c]\ \ge\ \tfrac23\,n\log_b n-C\,n\log_b(2\alpha).$$
--
--   In both cases the input can be taken with doubling dimension $\mathrm{ddim}(d_x)\le 2$. In particular, for fixed $\alpha$ and $b$ the bound is $\Omega_\alpha(n\log n)$: even approximate MSTs of points on a line cannot be found with $o(n\log n)$ comparisons.
--
--   **Formalization Note** The model is `DoublingMST.Supplement.ComparisonAlg`: a comparison is any $b$-outcome test of the metric, which contains the atomic distance comparisons of Definition 6.1 and finite-outcome comparisons of computed reals. For every input, the comparison count and the success event are assumed measurable in $\omega$. $\log_b$ is the real logarithm to base $b$.
--
--   Differences from the source:
--   - generalization: b-ary comparison algorithm (comparisons of computed reals with at most b outcomes) → a strategy whose tests are arbitrary b-outcome functions of the input metric, with free computation between tests; reason: Lemma 6.4's counting uses only b-ary branching and a fixed output per leaf; the source's comparisons are special tests, so the Lean lower bound implies the source's
--   - reading: a labeled set of n points on the real line → the algorithm sees the input only through its labelled metric lineMetric x (u, v) = |x u − x v|, not through the positions x; reason: §6.1 (p.30) gives the algorithm point labels without geometric information and comparisons of distances, and the proof (Lemma 6.5) counts the n!/2 distinct labelled metrics, identifying a placement with its reversal
--   - encoding: O(n log_b(2α)) in both bounds → one absolute C > 0 for all n ≥ 2, b ≥ 2, α ≥ 1 and both clauses; reason: the proof's error term comes from Stirling, the factor 2 of reversals and k_{n,α} ≤ n(2eα)^{n−1}, each at most an absolute multiple of n log_b(2α)
--   - encoding: deterministic or Las Vegas; succeeds with probability at least 2/3 → clause 1: success probability 1 on every input (deterministic = one-point Ω); clause 2: success probability ≥ 2/3 on every input; reason: a Las Vegas algorithm always outputs a valid tree; a deterministic algorithm is a randomized one with a one-point probability space
--   - encoding: a randomized algorithm → a family A : Ω → CmpStrategy n b over a probability space (Ω, μ), with the comparison count and the success event measurable in ω for every input; reason: the probabilities and expectations of the source are those of measurable quantities; without measurability μ and ∫⁻ would be outer measure and lower integral
--   - encoding: worst-case expected complexity on every labeled set of n points on the real line; the input metrics have doubling dimension at most 2 → ∃ injective x : Fin n → ℝ with ddim(lineMetric x) ≤ 2 and ∫⁻ cmpCount ≥ ofReal(bound); reason: the worst case is attained by some input; every input metric is a line metric of ddim ≤ 2 (Lemma 6.5's argument), so the witness carries that bound
--   - encoding: In particular, for fixed α and b the bound is Ω_α(n log n) → not a separate clause; reason: it follows from clauses 1 and 2: n log_b n − C n log_b(2α) ≥ ½ n log_b n once n ≥ (2α)^{2C}, and (2/3) n log_b n − C n log_b(2α) ≥ (1/3) n log_b n once n ≥ (2α)^{3C}
--   - encoding: n points → n ≥ 2; reason: the standing |X| ≥ 2 of p.11
-- source:
--   Höckendorff–Hommelsheim–Sohler–Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 6.3, p.31 (PDF p.33); proof p.34 (PDF p.36) via Lemmas 6.4–6.6

import Mathlib
import Definitions.Def_DoublingMST_Supplement_ComparisonAlg
import Definitions.Def_DoublingMST_Supplement_lineMetric
import Definitions.Def_DoublingMST_Supplement_IsApproxTree
import Definitions.Def_DoublingMST_ddim
open scoped Classical ENNReal

namespace DoublingMST.Supplement

open MeasureTheory

/-- **Theorem 6.3 (n log n comparison lower bound).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning
Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 6.3,
p.31 (PDF p.33): "Fix an integer b ≥ 2 and a factor α ≥ 1. Any b-ary comparison algorithm that
outputs an explicit α-approximate MST on every labeled set of n points on the real line requires,
in worst-case expected complexity, n log_b n − O(n log_b(2α)) comparisons if it is deterministic or
Las Vegas, and (2/3) n log_b n − O(n log_b(2α)) if it succeeds with probability at least 2/3 on
every input. In particular, for fixed α and b the bound is Ω_α(n log n). The input metrics have
doubling dimension at most 2."

There is an absolute `C > 0` such that for all `n ≥ 2`, `b ≥ 2`, `α ≥ 1` and every randomized
`b`-ary comparison algorithm `A` over a probability space `(Ω, μ)`:
1. if on every injective `x : Fin n → ℝ` the algorithm outputs an `α`-approximate spanning tree
   with probability `1`, then on some injective `x` (whose metric has doubling dimension at most 2)
   the expected number of comparisons is at least `n log_b n − C n log_b(2α)`;
2. if it does so with probability at least `2/3` on every such input, then on some such input the
   expected number of comparisons is at least `(2/3) n log_b n − C n log_b(2α)`.

**Formalization Note.** Comparisons are arbitrary `b`-outcome tests of the input metric
(`Definitions.Def_DoublingMST_Supplement_ComparisonAlg`); a deterministic algorithm is the case of
a one-point `Ω`. For every input the comparison count and the success event are assumed
measurable in the randomness. `log_b` is `Real.logb b`. -/
theorem theorem_6_3 : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n → ∀ b : ℕ, 2 ≤ b → ∀ α : ℝ, 1 ≤ α →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (A : Ω → CmpStrategy n b),
      (∀ x : Fin n → ℝ, Function.Injective x →
        Measurable (fun ω => cmpCount (A ω) (lineMetric x)) ∧
        MeasurableSet {ω | ∃ T, CmpOutputs (A ω) (lineMetric x) T ∧
          IsApproxTree (lineMetric x) α T}) →
      ((∀ x : Fin n → ℝ, Function.Injective x →
          μ {ω | ∃ T, CmpOutputs (A ω) (lineMetric x) T ∧ IsApproxTree (lineMetric x) α T} = 1) →
        ∃ x : Fin n → ℝ, Function.Injective x ∧ DoublingMST.ddim (lineMetric x) ≤ 2 ∧
          ENNReal.ofReal ((n : ℝ) * Real.logb b n - C * n * Real.logb b (2 * α)) ≤
            ∫⁻ ω, ((cmpCount (A ω) (lineMetric x) : ℕ∞) : ℝ≥0∞) ∂μ) ∧
      ((∀ x : Fin n → ℝ, Function.Injective x →
          (2 / 3 : ℝ≥0∞) ≤
            μ {ω | ∃ T, CmpOutputs (A ω) (lineMetric x) T ∧ IsApproxTree (lineMetric x) α T}) →
        ∃ x : Fin n → ℝ, Function.Injective x ∧ DoublingMST.ddim (lineMetric x) ≤ 2 ∧
          ENNReal.ofReal (2 / 3 * (n : ℝ) * Real.logb b n - C * n * Real.logb b (2 * α)) ≤
            ∫⁻ ω, ((cmpCount (A ω) (lineMetric x) : ℕ∞) : ℝ≥0∞) ∂μ) := by sorry

end DoublingMST.Supplement
