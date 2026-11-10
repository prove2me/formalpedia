-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_lemma_2_21
-- name    : DistRobustHalfspace.Main.lemma_2_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:18:25.014961+00:00
-- url     : https://prove2.me/theorems/9f91503a-5dc5-4566-b758-74900400b9e3
-- title:
--   Lemma 2.21 — threshold estimator with O(1/ε¹²) queries and samples
-- statement:
--   Under the standing assumptions of §§2–3. There is an algorithm which, given query access to $f$ and sample access to $D$, uses $O(1/\varepsilon^{12})$ queries and samples. It always outputs either $\bot$ or a real number $\hat t$ with $|\hat t|\le T_\varepsilon$. With probability at least $99/100$, both hold:
--   1. if $|\mathbb E_{y\sim D}[f(y)]|\le1-\varepsilon$, it outputs a real number $\hat t$;
--   2. if $f$ is a halfspace and $D$ is the standard Gaussian, it outputs either $\bot$ or a real number $\hat t$ that is an $\varepsilon^4$-good threshold estimate for $f$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §§2–3 (p. 11): n ≥ n₀, ε ≤ ε₀, ε ≥ 1/n for suitable absolute constants n₀, ε₀ → `∃ n₀ ε₀ > 0` quantified before the tester and its inputs, with hypotheses `n₀ ≤ n`, `ε ≤ ε₀`, `1/n ≤ ε`; reason: the section's standing assumptions, stated as binders (FAITHFULNESS_TRAPS row 19)
--   - generalization: "there is an algorithm" → there is a non-adaptive `Tester` (query points fixed by samples and internal randomness); reason: a non-adaptive algorithm is an algorithm, so the Lean statement implies the source's; the algorithm in the paper's proof is non-adaptive
--   - encoding: randomized algorithm with sample access to D and query access to f → `Tester`: i.i.d. samples from D, an internal seed on an arbitrary probability space, query points a function of samples and seed, output a function of samples, seed and answers, worst-case counts; jointly measurable (`IsMeasurable`); reason: the paper's model of a tester; measurability makes the output probabilities those of events
--   - encoding: output ⊥ or a real number t̂ → output in `Option ℝ` (`none` = ⊥); |t̂| ≤ T_ε on every run (`∀ S ω`); reason: the bound on t̂ is a property of every output, not of an event
--   - reading: "f is a halfspace" ⇒ ⊥ or an ε⁴-good t̂ → `IsHalfspace f` (w = 0 allowed) ⇒ every real output t̂ satisfies `IsGoodThreshold f (ε⁴) t̂`; reason: ε⁴-good is defined only for unit-normal halfspaces (Definition 2.4), so for a constant f only ⊥ qualifies
--   - reading: sign(⟨w, x⟩ − t) with sign(0) unspecified → `sgn 0 = 1` (sign(0) = +1); reason: the paper never fixes sign(0); a {±1}-valued sign needs a value there
--   - encoding: "with probability at least p" → `p ≤ T.prob D f E` in `ℝ≥0∞` (product of D^{⊗samples} and the seed's law); reason: probabilities of events of a measurable tester
--   - encoding: Borel f : ℝⁿ → {±1} (footnote 1) → `f : Rn n → ℝ` with `IsBoolFn f` (measurable, values ±1); reason: real values make f(x)·x and f(y)(⟨y, v⟩ − t) direct; same functions
--   - encoding: Borel probability distribution D on ℝⁿ (footnote 1) → `D : ProbabilityMeasure (Rn n)`; reason: same objects
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Lemma 2.21, p. 23 (PDF 25)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Lemma 2.21 (p. 23), threshold estimator: a tester using `O(1/ε^{12})` queries and samples whose
output is `⊥` (`none`) or a real `t̂` with `|t̂| ≤ T_ε`, such that with probability at least
`99/100`: if `|E_{y∼D}[f(y)]| ≤ 1 − ε` it outputs a real number; if `f` is a halfspace and
`D = N(0, Iₙ)` it outputs `⊥` or an `ε⁴`-good threshold estimate for `f`. -/
theorem lemma_2_21 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → 1 / (n : ℝ) ≤ ε →
      ∃ A : Tester n (Option ℝ), A.IsMeasurable ∧
        (A.numSamples : ℝ) ≤ C / ε ^ 12 ∧ (A.numQueries : ℝ) ≤ C / ε ^ 12 ∧
        (∀ f : Rn n → ℝ, IsBoolFn f → ∀ S ω (t' : ℝ), A.run f S ω = some t' → |t'| ≤ Teps ε) ∧
        ∀ (D : ProbabilityMeasure (Rn n)) (f : Rn n → ℝ), IsBoolFn f →
          (99 / 100 : ℝ≥0∞) ≤ A.prob D f (fun o =>
            (|∫ y, f y ∂(D : Measure (Rn n))| ≤ 1 - ε → o ≠ none) ∧
            (IsHalfspace f ∧ D = gaussPM n →
              ∀ t' : ℝ, o = some t' → IsGoodThreshold f (ε ^ 4) t')) := by sorry

end DistRobustHalfspace.Main
