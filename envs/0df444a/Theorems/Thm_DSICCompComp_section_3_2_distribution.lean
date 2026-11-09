-- Prove2me | Theorems.Thm_DSICCompComp_section_3_2_distribution
-- name    : DSICCompComp.section_3_2_distribution
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:30:47.808314+00:00
-- url     : https://prove2.me/theorems/5f2814e0-6fb7-4d4d-8e8e-9a2558d36c47
-- title:
--   §3.2 — the hard distribution $D$: support $[ab,\infty)$, CDF, virtual value, regularity
-- statement:
--   Let $a \ge 1$ and $b \in (0,1)$, and let $D$ be the distribution of $a\cdot\min\{bZ,1\} + (bZ-1)_+$ with $Z \sim \mathcal{ER}$ (CDF $1 - 1/x$ on $[1,\infty)$). Then the support of $D$ is $[ab, +\infty)$, its CDF is
--   $$
--   F(x) = \begin{cases} 0 & x < ab,\\ 1 - ab/x & ab \le x \le a,\\ 1 - b/(x - a + 1) & x \ge a,\end{cases}
--   $$
--   $D$ has a density $f$ whose virtual value is
--   $$
--   \varphi(x) = x - \frac{1 - F(x)}{f(x)} = \begin{cases} 0 & ab \le x < a,\\ a - 1 & x > a,\end{cases}
--   $$
--   and, since $\varphi$ is nondecreasing, $D$ is regular. Consequently $D^m$ is a regular product distribution.
--
--   This is the distribution that witnesses Theorem 3.1: it is regular, yet its equal-revenue tail above $a$ is what makes extra bidders valuable to a selling-separately auction but not enough to catch up with the mechanism $M$.
--
--   Differences from the source:
--   - encoding: D a distribution on [ab, ∞) ⊂ ℝ → a probability measure on ℝ≥0, with CDF and density those of its pushforward to ℝ; reason: the values are nonnegative; same distribution
--   - reading: the CDF and the virtual value function of D → the CDF clauses, and ∃ a measurable density version f of the pushforward with the stated virtual values; reason: a density is defined up to null sets; the virtual value is that of a suitable version
--   - encoding: the support of each marginal is [ab, +∞) → F(x) = 0 for x < ab, together with the CDF formulas (strictly increasing on [ab, ∞)); reason: the CDF determines the support
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.2, p.11 (pdf p.12)

import Mathlib
import Definitions.Def_DSICCompComp_IsRegular
import Definitions.Def_DSICCompComp_hardDist

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- §3.2, the hard distribution `D` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, §3.2, p.11 (pdf p.12)).
For `a ≥ 1` and `b ∈ (0, 1)`, let `D` be the law of `a·min{bZ, 1} + (bZ − 1)₊` with `Z ∼ ℰℛ`, and
`F` its CDF. Then `F(x) = 0` for `x < ab` (the support is `[ab, +∞)`), `F(x) = 1 − ab/x` on
`[ab, a]`, `F(x) = 1 − b/(x − a + 1)` for `x ≥ a`; `D` has a density version whose virtual value
`φ(x) = x − (1 − F(x))/f(x)` is `0` on `[ab, a)` and `a − 1` on `(a, ∞)`; and `D` is regular.

**Formalization Note** `D` lives on `ℝ≥0` and its CDF and density are those of the pushforward to
`ℝ`. -/
theorem section_3_2_distribution (a b : ℝ) (ha : 1 ≤ a) (hb0 : 0 < b) (hb1 : b < 1) :
    (∀ x : ℝ, x < a * b →
        cdf ((hardDist a b : Measure ℝ≥0).map (fun y : ℝ≥0 => (y : ℝ))) x = 0) ∧
    (∀ x : ℝ, a * b ≤ x → x ≤ a →
        cdf ((hardDist a b : Measure ℝ≥0).map (fun y : ℝ≥0 => (y : ℝ))) x = 1 - a * b / x) ∧
    (∀ x : ℝ, a ≤ x →
        cdf ((hardDist a b : Measure ℝ≥0).map (fun y : ℝ≥0 => (y : ℝ))) x = 1 - b / (x - a + 1)) ∧
    (∃ f : ℝ → ℝ≥0∞, Measurable f ∧
        (hardDist a b : Measure ℝ≥0).map (fun y : ℝ≥0 => (y : ℝ)) = volume.withDensity f ∧
        (∀ x ∈ Set.Ico (a * b) a,
          x - (1 - cdf ((hardDist a b : Measure ℝ≥0).map (fun y : ℝ≥0 => (y : ℝ))) x) /
            (f x).toReal = 0) ∧
        (∀ x ∈ Set.Ioi a,
          x - (1 - cdf ((hardDist a b : Measure ℝ≥0).map (fun y : ℝ≥0 => (y : ℝ))) x) /
            (f x).toReal = a - 1)) ∧
    IsRegular (hardDist a b : Measure ℝ≥0) := by sorry

end DSICCompComp
