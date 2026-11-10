-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_lemma_3_2
-- name    : DistRobustHalfspace.Main.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:19:14.777716+00:00
-- url     : https://prove2.me/theorems/961e878e-318e-4b97-8798-4b7dd7770ef8
-- title:
--   Lemma 3.2 — Algorithm 1 accepts a halfspace under N(0, Iₙ) with probability ≥ 3/4
-- statement:
--   Suppose $f$ is a halfspace and $D$ is the standard Gaussian. Then Algorithm 1 accepts with probability at least $3/4$.
--
--   This holds for all sufficiently large $\Theta(\cdot)$ constants of Algorithm 1, under the standing assumptions $n\ge n_0$, $\varepsilon\le\varepsilon_0$, $\varepsilon\ge1/n$ for $\varepsilon=\varepsilon^*/2$, where $\varepsilon^*\in(0,1)$ is the algorithm's input.
--
--   Differences from the source:
--   - reading: Algorithm 1 (p. 26), whose line 2 and line 4 run "the algorithms from Lemmas 2.15, 2.19, 2.20, 2.21" and whose Θ(·) constants are unspecified → `alg1 P n ε∗`: Algorithm 1 with the algorithms constructed in the proofs of Lemmas 2.21 (p. 23), 2.15 (p. 18), 2.19 (p. 21), 2.20 (p. 22), and the constants `P : Alg1Consts`; reason: the lemmas' algorithms are the ones their proofs construct; the Θ(·)/L constants are parameters
--   - reading: Θ(·) with "sufficiently large" constants, and absolute n₀, ε₀ → `∃ c₀, ∀ P, P.AllAtLeast c₀ → ∃ n₀ ε₀ …` (n₀, ε₀ chosen after the constants); reason: constants are fixed first, then the standing thresholds n₀, ε₀ (§2.1)
--   - encoding: standing assumptions n ≥ n₀, ε ≤ ε₀, ε ≥ 1/n for the analysis parameter ε = ε∗/2 (§3, p. 24), input ε∗ ∈ (0, 1) → hypotheses `n₀ ≤ n`, `0 < ε∗ < 1`, `ε∗/2 ≤ ε₀`, `1/n ≤ ε∗/2`; reason: Algorithm 1's input range and the standing assumptions of §§2–3 on ε = ε∗/2
--   - reading: "halfspace" (p. 1: sign(⟨w, x⟩ − t), w ∈ ℝⁿ, t ∈ ℝ) → `IsHalfspace f`: ∃ w t, ∀ x, f x = sgn(⟪w, x⟫ − t), with w = 0 (both constants) allowed; reason: p. 1 allows every w ∈ ℝⁿ; this includes both constant classifiers, including the zero-normal classifier used in Lemma 2.11
--   - reading: sign(⟨w, x⟩ − t) with sign(0) unspecified → `sgn 0 = 1` (sign(0) = +1); reason: the paper never fixes sign(0); a {±1}-valued sign needs a value there
--   - encoding: "with probability at least p" → `p ≤ T.prob D f E` in `ℝ≥0∞` (product of D^{⊗samples} and the seed's law); reason: probabilities of events of a measurable tester
--   - encoding: Borel f : ℝⁿ → {±1} (footnote 1) → `f : Rn n → ℝ` with `IsBoolFn f` (measurable, values ±1); reason: real values make f(x)·x and f(y)(⟨y, v⟩ − t) direct; same functions
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Lemma 3.2, p. 25 (PDF 27)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
import Definitions.Def_DistRobustHalfspace_Main_Algorithm1
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Lemma 3.2 (p. 25): if `f` is a halfspace and `D = N(0, Iₙ)`, Algorithm 1 accepts with probability at
least `3/4` (its `Θ(·)` constants sufficiently large; standing assumptions `n ≥ n₀`, `ε ≤ ε₀`,
`ε ≥ 1/n` for `ε = ε∗/2`). -/
theorem lemma_3_2 :
    ∃ c₀ : ℝ, ∀ P : Alg1Consts, P.AllAtLeast c₀ → ∃ n₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ εstar : ℝ, 0 < εstar → εstar < 1 → εstar / 2 ≤ ε₀ →
        1 / (n : ℝ) ≤ εstar / 2 →
      ∀ f : Rn n → ℝ, IsBoolFn f → IsHalfspace f →
        (3 / 4 : ℝ≥0∞) ≤ (alg1 P n εstar).prob (gaussPM n) f (fun o => o = true) := by sorry

end DistRobustHalfspace.Main
