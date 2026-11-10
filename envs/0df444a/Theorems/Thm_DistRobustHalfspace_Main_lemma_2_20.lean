-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_lemma_2_20
-- name    : DistRobustHalfspace.Main.lemma_2_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:18:26.639569+00:00
-- url     : https://prove2.me/theorems/1d964a6e-a876-4002-a79d-aab3dade8853
-- title:
--   Lemma 2.20 — weighted centroid tester
-- statement:
--   Under the standing assumptions of §§2–3. There is an algorithm which, given any neighborhood $p$-tuple $N$, query access to $f$ and sample access to $D$, uses $O(\sqrt nR_\varepsilon^2)$ samples and $O(p\sqrt nR_\varepsilon^2)$ queries. It accepts or rejects so that, with probability at least $99/100$, both hold:
--   1. if $f$ is a halfspace and $D$ is the standard Gaussian, it accepts;
--   2. if $D$ is supported only on the $2\sqrt n$-radius ball centered at the origin and $\|\mathbb E_{y\sim D}[f(y)\hat\alpha_{f,N}(y)\,y]\|_2^2>4(\sqrt n+R_\varepsilon^2)$, it rejects.
--
--   Differences from the source:
--   - encoding: standing assumptions of §§2–3 (p. 11): n ≥ n₀, ε ≤ ε₀, ε ≥ 1/n for suitable absolute constants n₀, ε₀ → `∃ n₀ ε₀ > 0` quantified before the tester family and its inputs, with hypotheses `n₀ ≤ n`, `ε ≤ ε₀`, `1/n ≤ ε`; reason: the section's standing assumptions, stated as binders (FAITHFULNESS_TRAPS row 19)
--   - generalization: "there is an algorithm" → there is a non-adaptive `Tester` (query points fixed by samples and internal randomness); reason: a non-adaptive algorithm is an algorithm, so the Lean statement implies the source's; the algorithm in the paper's proof is non-adaptive
--   - encoding: randomized algorithm with sample access to D and query access to f → `Tester`: i.i.d. samples from D, an internal seed on an arbitrary probability space, query points a function of samples and seed, output a function of samples, seed and answers, worst-case counts; jointly measurable (`IsMeasurable`); reason: the paper's model of a tester; measurability makes the output probabilities those of events
--   - encoding: "given any neighborhood p-tuple N" → a family `A p N`, for every `p ≥ 1` and `N : Fin p → Rn n`; reason: ℓ_{f,N} averages over the p points of N, undefined for p = 0
--   - reading: "halfspace" (p. 1: sign(⟨w, x⟩ − t), w ∈ ℝⁿ, t ∈ ℝ) → `IsHalfspace f`: ∃ w t, ∀ x, f x = sgn(⟪w, x⟫ − t), with w = 0 (both constants) allowed; reason: p. 1 allows every w ∈ ℝⁿ; this includes both constant classifiers, including the zero-normal classifier used in Lemma 2.11
--   - reading: sign(⟨w, x⟩ − t) with sign(0) unspecified → `sgn 0 = 1` (sign(0) = +1); reason: the paper never fixes sign(0); a {±1}-valued sign needs a value there
--   - encoding: "with probability at least p" → `p ≤ T.prob D f E` in `ℝ≥0∞` (product of D^{⊗samples} and the seed's law); reason: probabilities of events of a measurable tester
--   - encoding: Borel f : ℝⁿ → {±1} (footnote 1) → `f : Rn n → ℝ` with `IsBoolFn f` (measurable, values ±1); reason: real values make f(x)·x and f(y)(⟨y, v⟩ − t) direct; same functions
--   - encoding: Borel probability distribution D on ℝⁿ (footnote 1) → `D : ProbabilityMeasure (Rn n)`; reason: same objects
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Lemma 2.20, p. 22 (PDF 24)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Lemma 2.20 (p. 22), weighted centroid tester: given a neighborhood `p`-tuple `N`, a tester using
`O(√n R_ε²)` samples and `O(p √n R_ε²)` queries that with probability at least `99/100` accepts if
`f` is a halfspace and `D = N(0, Iₙ)`, and rejects if `D` is supported on the `2√n`-ball and
`‖E_{y∼D}[f(y) α̂_{f,N}(y) y]‖₂² > 4(√n + R_ε²)`. -/
theorem lemma_2_20 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → 1 / (n : ℝ) ≤ ε →
      ∃ A : (p : ℕ) → (Fin p → Rn n) → Tester n Bool, ∀ (p : ℕ) (N : Fin p → Rn n), 0 < p →
        (A p N).IsMeasurable ∧
        ((A p N).numSamples : ℝ) ≤ C * Real.sqrt n * Reps ε ^ 2 ∧
        ((A p N).numQueries : ℝ) ≤ C * p * Real.sqrt n * Reps ε ^ 2 ∧
        ∀ (D : ProbabilityMeasure (Rn n)) (f : Rn n → ℝ), IsBoolFn f →
          (99 / 100 : ℝ≥0∞) ≤ (A p N).prob D f (fun o =>
            (IsHalfspace f ∧ D = gaussPM n → o = true) ∧
            (SupportedInBall (D : Measure (Rn n)) ∧
                4 * (Real.sqrt n + Reps ε ^ 2) <
                  ‖weightedCentroid ε f N (D : Measure (Rn n))‖ ^ 2 → o = false)) := by sorry

end DistRobustHalfspace.Main
