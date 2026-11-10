-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_theorem_2_1
-- name    : DistRobustHalfspace.Main.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:19:29.663388+00:00
-- url     : https://prove2.me/theorems/86b7d8bc-653c-41f4-958c-cc17f5ae2da0
-- title:
--   Theorem 2.1 — picky tester with O(n^{2/3}/ε³⁸) samples and queries; Algorithm 1 in its analysis range
-- statement:
--   There is a distribution-picky tester for halfspaces with respect to the standard Gaussian over $\mathbb R^n$, with sample and query complexity $O(n^{2/3}/\varepsilon^{38})$.
--
--   For every sufficiently large choice $P$ of the algorithm constants, there are uniform constants $C>0$, $n_0$, and $\varepsilon_0>0$. For every dimension $n$ and every $\varepsilon^*>0$, there exists a non-adaptive tester $T$ that is $(\mathcal N(0,I_n),\text{all distributions})$-picky and uses at most $C n^{2/3}/(\varepsilon^*)^{38}$ samples and queries. In the analysis range $n\ge n_0$, $0<\varepsilon^*<1$, and $1/n\le\varepsilon^*/2\le\varepsilon_0$, this tester equals `alg1 P n εstar`. Outside that range the existence clause retains the paper's elementary/PAC fallback (§2.1, PDF 13).
--
--   Differences from the source:
--   - reading: Algorithm 1 (p. 26), whose line 2 and line 4 run "the algorithms from Lemmas 2.15, 2.19, 2.20, 2.21" and whose Θ(·) constants are unspecified → `alg1 P n ε∗`: Algorithm 1 with the algorithms constructed in the proofs of Lemmas 2.21 (p. 23), 2.15 (p. 18), 2.19 (p. 21), 2.20 (p. 22), and the constants `P : Alg1Consts`; reason: the lemmas' algorithms are the ones their proofs construct; the Θ(·)/L constants are parameters
--   - reading: Θ(·) with "sufficiently large" constants, and absolute n₀, ε₀ → `∃ c₀, ∀ P, P.AllAtLeast c₀ → ∃ n₀ ε₀ …` (n₀, ε₀ chosen after the constants); reason: constants are fixed first, then the standing thresholds n₀, ε₀ (§2.1)
--   - reading: Theorem 2.1 states the tester upper bound; §2.1 restricts the analysis and explicitly invokes PAC testing for ε < 1/n → a tester exists for all n and ε∗ > 0, with equality to Algorithm 1 in its analysis range; reason: the standing assumptions delimit the analysis of Algorithm 1 and do not discard the remaining instances of the announced upper bound
--   - encoding: "distribution-picky tester ... with respect to the standard Gaussian" → `IsPickyTester T (gaussPM n) Set.univ ε∗` for all n and ε∗ > 0; reason: p. 4: the upper bound is picky testing with D∗ = N(0, Iₙ) and A the set of all distributions
--   - reading: "the following hold with probability at least 3/4" (Definition 1.6) → one event: the conjunction of Completeness and Soundness has probability ≥ 3/4; reason: the literal reading; it implies each clause separately
--   - reading: "halfspace" (p. 1: sign(⟨w, x⟩ − t), w ∈ ℝⁿ, t ∈ ℝ) → `IsHalfspace f`: ∃ w t, ∀ x, f x = sgn(⟪w, x⟫ − t), with w = 0 (both constants) allowed; reason: p. 1 allows every w ∈ ℝⁿ; this includes both constant classifiers, including the zero-normal classifier used in Lemma 2.11
--   - reading: sign(⟨w, x⟩ − t) with sign(0) unspecified → `sgn 0 = 1` (sign(0) = +1); reason: the paper never fixes sign(0); a {±1}-valued sign needs a value there
--   - encoding: O(·) bounds → explicit constants `C > 0` quantified before n, ε and every input; reason: the paper's O(·) constants are absolute (§2.1, footnote 2)
--   - encoding: Borel f : ℝⁿ → {±1} (footnote 1) → `f : Rn n → ℝ` with `IsBoolFn f` (measurable, values ±1); reason: real values make f(x)·x and f(y)(⟨y, v⟩ − t) direct; same functions
--   - generalization: a distribution-picky tester with the stated sample and query complexity → the tester is non-adaptive; reason: Algorithm 1 and the sample-based PAC fallback use non-adaptive queries; forgetting this property recovers the full printed claim
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Theorem 2.1, p. 10 (PDF 12)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
import Definitions.Def_DistRobustHalfspace_Main_Algorithm1
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Theorem 2.1 (p. 10): a `(N(0, Iₙ), all distributions)`-picky halfspace tester
with sample and query complexity `O(n^{2/3}/ε^{38})` for every dimension and proximity.
It is Algorithm 1 in the analysis range `n ≥ n₀`, `1/n ≤ ε∗/2 ≤ ε₀`, `ε∗ < 1`.
Outside this range the paper permits the elementary/PAC testing fallback (§2.1, p. 11).
The `Θ(·)` constants are sufficiently large, and all bounds are uniform in `n, ε∗`. -/
theorem theorem_2_1 :
    ∃ c₀ : ℝ, ∀ P : Alg1Consts, P.AllAtLeast c₀ → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (n : ℕ) (εstar : ℝ), 0 < εstar → ∃ T : Tester n Bool,
        IsPickyTester T (gaussPM n) Set.univ εstar ∧
        (T.numSamples : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) / εstar ^ 38 ∧
        (T.numQueries : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) / εstar ^ 38 ∧
        (n₀ ≤ n → εstar < 1 → εstar / 2 ≤ ε₀ → 1 / (n : ℝ) ≤ εstar / 2 →
          T = alg1 P n εstar) := by sorry

end DistRobustHalfspace.Main
