-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_lemma_2_19
-- name    : DistRobustHalfspace.Main.lemma_2_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:18:37.54622+00:00
-- url     : https://prove2.me/theorems/efd656bc-a518-4bf3-b9de-ede49bb6757f
-- title:
--   Lemma 2.19 — Frobenius tester with O(√n) samples
-- statement:
--   Under the standing assumption $n\ge n_0$. There is an algorithm which, given sample access to a distribution $D$, draws $O(\sqrt n)$ samples from $D$ and accepts or rejects so that, with probability at least $99/100$, both hold:
--   1. if $D$ is the standard Gaussian, it accepts;
--   2. if $D$ is supported only on the $2\sqrt n$-radius ball centered at the origin and $\|\mathbb E_{y\sim D}[yy^\top]\|_F>2\sqrt n$, it rejects.
--
--   Differences from the source:
--   - encoding: standing assumption n ≥ n₀ (p. 11) → `∃ n₀, ∀ n ≥ n₀`; reason: the statement involves no ε, so ε ≤ ε₀ and ε ≥ 1/n do not apply
--   - encoding: an algorithm with sample access only → a `Tester` with `numQueries = 0`; its output law does not depend on the (arbitrary Boolean) f; reason: the tester model of the mission; zero queries is sample access only
--   - encoding: randomized algorithm with sample access to D and query access to f → `Tester`: i.i.d. samples from D, an internal seed on an arbitrary probability space, query points a function of samples and seed, output a function of samples, seed and answers, worst-case counts; jointly measurable (`IsMeasurable`); reason: the paper's model of a tester; measurability makes the output probabilities those of events
--   - encoding: "with probability at least p" → `p ≤ T.prob D f E` in `ℝ≥0∞` (product of D^{⊗samples} and the seed's law); reason: probabilities of events of a measurable tester
--   - encoding: Borel probability distribution D on ℝⁿ (footnote 1) → `D : ProbabilityMeasure (Rn n)`; reason: same objects
--   - encoding: ‖E_{y∼D}[yyᵀ]‖_F → `frobNorm (secondMoment D)` with Bochner-integral entries; reason: in condition 2 D is supported on the ball, so the entries are integrable
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Lemma 2.19, p. 20 (PDF 22)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Lemma 2.19 (p. 20), Frobenius tester: a sample-only tester drawing `O(√n)` samples from `D` that
with probability at least `99/100` accepts if `D = N(0, Iₙ)`, and rejects if `D` is supported on
the `2√n`-ball and `‖E_{y∼D}[y yᵀ]‖_F > 2√n` (for `n ≥ n₀`, the standing assumption). -/
theorem lemma_2_19 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ A : Tester n Bool, A.IsMeasurable ∧ A.numQueries = 0 ∧
        (A.numSamples : ℝ) ≤ C * Real.sqrt n ∧
        ∀ (D : ProbabilityMeasure (Rn n)) (f : Rn n → ℝ), IsBoolFn f →
          (99 / 100 : ℝ≥0∞) ≤ A.prob D f (fun o =>
            (D = gaussPM n → o = true) ∧
            (SupportedInBall (D : Measure (Rn n)) ∧
                2 * Real.sqrt n < frobNorm (secondMoment (D : Measure (Rn n))) → o = false)) := by sorry

end DistRobustHalfspace.Main
