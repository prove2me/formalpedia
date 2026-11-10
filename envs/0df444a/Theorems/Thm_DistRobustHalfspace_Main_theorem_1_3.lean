-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_theorem_1_3
-- name    : DistRobustHalfspace.Main.theorem_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:17:37.771858+00:00
-- url     : https://prove2.me/theorems/c8e4e253-3051-4a4f-b50d-a7ecdbb9597f
-- title:
--   Theorem 1.3 — an N(0, Iₙ)-robust halfspace tester with O(n^{2/3} poly(1/ε)) non-adaptive queries
-- statement:
--   There is an $\mathcal N(0,I_n)$-robust halfspace tester which uses only $O(n^{2/3}\operatorname{poly}(1/\varepsilon))$ non-adaptive queries.
--
--   In the Lean statement there are constants $C>0$ and $k$ such that, for every dimension $n$ and every proximity parameter $\varepsilon>0$, there is a randomized tester with the following properties. It depends only on $n$ and $\varepsilon$, has sample access to an arbitrary Borel distribution $D$ on $\mathbb R^n$ and non-adaptive query access to a Borel $f:\mathbb R^n\to\{\pm1\}$, and makes at most $C\,n^{2/3}(1/\varepsilon)^k$ queries. It outputs Accept, Reject or Tantrum, and for every $D$ and $f$ the following hold together with probability at least $3/4$:
--   - if $f$ is a halfspace, it does not Reject;
--   - if $f$ is $\varepsilon$-far from every halfspace under $D$, it does not Accept;
--   - if $D=\mathcal N(0,I_n)$, it does not Tantrum.
--
--   Differences from the source:
--   - encoding: O(n^{2/3} poly(1/ε)) queries → `numQueries ≤ C · n^{2/3} · (1/ε)^k` with `C > 0`, `k` quantified before n and ε; reason: O(·) and poly(1/ε) have constants independent of n, ε, D and f (footnote 2)
--   - encoding: randomized algorithm with sample access to D and query access to f → `Tester`: i.i.d. samples from D, an internal seed on an arbitrary probability space, query points a function of samples and seed, output a function of samples, seed and answers, worst-case counts; jointly measurable (`IsMeasurable`); reason: the paper's model of a tester; measurability makes the output probabilities those of events
--   - reading: "the following hold with probability at least 3/4" (Definition 1.2) → one event: the conjunction of Completeness, Soundness and Assertiveness has probability ≥ 3/4; reason: the literal reading; it implies the three separate bounds
--   - reading: "halfspace" (p. 1: sign(⟨w, x⟩ − t), w ∈ ℝⁿ, t ∈ ℝ) → `IsHalfspace f`: ∃ w t, ∀ x, f x = sgn(⟪w, x⟫ − t), with w = 0 (both constants) allowed; reason: p. 1 allows every w ∈ ℝⁿ; this includes both constant classifiers, including the zero-normal classifier used in Lemma 2.11
--   - reading: sign(⟨w, x⟩ − t) with sign(0) unspecified → `sgn 0 = 1` (sign(0) = +1); reason: the paper never fixes sign(0); a {±1}-valued sign needs a value there
--   - encoding: Borel f : ℝⁿ → {±1} (footnote 1) → `f : Rn n → ℝ` with `IsBoolFn f` (measurable, values ±1); reason: real values make f(x)·x and f(y)(⟨y, v⟩ − t) direct; same functions
--   - encoding: Borel probability distribution D on ℝⁿ (footnote 1) → `D : ProbabilityMeasure (Rn n)`; reason: same objects
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Theorem 1.3, p. 3 (PDF 5)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Theorem 1.3 (p. 3, Query Upper Bound): there is an `N(0, Iₙ)`-robust halfspace tester which uses
only `O(n^{2/3} poly(1/ε))` non-adaptive queries: constants `C`, `k` such that for every dimension
`n` and every proximity parameter `ε > 0` some tester (depending only on `n`, `ε`) makes at most
`C · n^{2/3} · (1/ε)^k` non-adaptive queries and is a `{N(0, Iₙ)}`-robust halfspace tester. -/
theorem theorem_1_3 :
    ∃ C k : ℝ, 0 < C ∧ ∀ (n : ℕ) (ε : ℝ), 0 < ε →
      ∃ T : Tester n Verdict,
        (T.numQueries : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) * (1 / ε) ^ k ∧
        IsRobustTester T {gaussPM n} ε := by sorry

end DistRobustHalfspace.Main
