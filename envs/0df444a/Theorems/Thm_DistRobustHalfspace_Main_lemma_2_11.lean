-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_lemma_2_11
-- name    : DistRobustHalfspace.Main.lemma_2_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:18:34.311227+00:00
-- url     : https://prove2.me/theorems/afdc51d4-5a28-4cd1-9019-e3b43779e2b6
-- title:
--   Lemma 2.11 — distance disagreement in the NO case: DD > ε³/32
-- statement:
--   Under the standing assumptions of §§2–3 ($n\ge n_0$, $\varepsilon\le\varepsilon_0$, $\varepsilon\ge1/n$): let $D$ be a distribution on $\mathbb R^n$ and $f:\mathbb R^n\to\{\pm1\}$ with $\operatorname{dist}_D(f,h)>\varepsilon$ for all halfspaces $h$. Let $\beta$ be any bounded measurable function with
--   $$\Pr_{y\sim D}[\beta(y)<\varepsilon/4]\le\varepsilon/2.\qquad(9)$$
--   Then for every $\hat t\in\mathbb R$, $\mathrm{DD}^{\hat t}_\beta(f,D)>\varepsilon^3/32$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §§2–3 (p. 11): n ≥ n₀, ε ≤ ε₀, ε ≥ 1/n for suitable absolute constants n₀, ε₀ → `∃ n₀ ε₀ > 0` quantified before n, ε, D, f, β, t̂, with hypotheses `n₀ ≤ n`, `ε ≤ ε₀`, `1/n ≤ ε`; reason: the section's standing assumptions, stated as binders (FAITHFULNESS_TRAPS row 19)
--   - reading: "halfspace" (p. 1: sign(⟨w, x⟩ − t), w ∈ ℝⁿ, t ∈ ℝ) → `IsHalfspace f`: ∃ w t, ∀ x, f x = sgn(⟪w, x⟫ − t), with w = 0 (both constants) allowed; reason: p. 1 allows every w ∈ ℝⁿ; this includes both constant classifiers, including the zero-normal classifier used in Lemma 2.11
--   - reading: sign(⟨w, x⟩ − t) with sign(0) unspecified → `sgn 0 = 1` (sign(0) = +1); reason: the paper never fixes sign(0); a {±1}-valued sign needs a value there
--   - encoding: Borel f : ℝⁿ → {±1} (footnote 1) → `f : Rn n → ℝ` with `IsBoolFn f` (measurable, values ±1); reason: real values make f(x)·x and f(y)(⟨y, v⟩ − t) direct; same functions
--   - encoding: Borel probability distribution D on ℝⁿ (footnote 1) → `D : ProbabilityMeasure (Rn n)`; reason: same objects
--   - encoding: DD^{t̂}_β(f, D) > ε³/32 → `ofReal(ε³/32) < DD β t̂ f D` in `ℝ≥0∞`; reason: DD is the expectation of a nonnegative function and may be +∞; +∞ > ε³/32 as on paper
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Lemma 2.11, p. 16 (PDF 18)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Lemma 2.11 (p. 16): NO case of the distance disagreement measure. If `dist_D(f, h) > ε` for all
halfspaces `h` and `β` is bounded measurable with `P_{y∼D}[β(y) < ε/4] ≤ ε/2` (9), then
`DD^{t̂}_β(f, D) > ε³/32` for every `t̂` (under the standing assumptions `n ≥ n₀`, `ε ≤ ε₀`,
`ε ≥ 1/n` of Sections 2–3). -/
theorem lemma_2_11 :
    ∃ n₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → 1 / (n : ℝ) ≤ ε →
      ∀ (D : ProbabilityMeasure (Rn n)) (f : Rn n → ℝ), IsBoolFn f → FarFromHalfspaces D f ε →
      ∀ β : Rn n → ℝ, Measurable β → (∃ M : ℝ, ∀ x, |β x| ≤ M) →
        ((D : Measure (Rn n)) {y | β y < ε / 4}).toReal ≤ ε / 2 →
        ∀ t' : ℝ, ENNReal.ofReal (ε ^ 3 / 32) < DD β t' f (D : Measure (Rn n)) := by sorry

end DistRobustHalfspace.Main
