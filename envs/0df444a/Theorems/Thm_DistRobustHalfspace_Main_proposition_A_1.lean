-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_proposition_A_1
-- name    : DistRobustHalfspace.Main.proposition_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:17:28.421002+00:00
-- url     : https://prove2.me/theorems/e99db882-d84d-4404-b4ba-dc18cc339b89
-- title:
--   Proposition A.1 — a distribution-robust tester under {D∗} from a (D∗, C)-picky tester at cost O(m + q)
-- statement:
--   Suppose $A$ is a $(D^*,C)$-picky halfspace tester, and let $m(n,\varepsilon)$ and $q(n,\varepsilon)$ be the sample and query cost of $A$. Then there is a distribution-robust tester for halfspaces under $\{D^*\}$ with sample and query cost $O(m(n,\varepsilon)+q(n,\varepsilon))$.
--
--   In the Lean statement there is an absolute constant $K$ such that the following holds for every $n$, every $D^*\in C$, and every family $A_\varepsilon$ ($\varepsilon>0$) of $(D^*,C)$-picky testers for $\varepsilon$. There is a family $B_\varepsilon$ of $\{D^*\}$-robust halfspace testers for $\varepsilon$ (Definition 1.2: guarantees for every input distribution) with at most $K(m+q)$ samples and at most $K(m+q)$ queries, where $m$ and $q$ are $A_\varepsilon$'s sample and query counts.
--
--   Both the input and output testers may make adaptive queries; the statement imposes no non-adaptivity restriction on A.
--
--   Differences from the source:
--   - encoding: randomized algorithm with sample access to D and query access to f → `AdaptiveTester`: finitely many i.i.d. samples, an independent probability-space seed, sequential queries depending on previous answers, and a measurable decision after the finite transcript; reason: Proposition A.1 permits adaptive input testers; padding early termination and drawing the bounded sample sequence in advance preserve worst-case costs and output laws
--   - encoding: a picky tester A with costs m(n, ε), q(n, ε) → for fixed n, a family `A ε` (ε > 0) with m, q its sample and query counts; the O-constant `K` is quantified before n; reason: the costs are functions of (n, ε); the O(·) constant is absolute
--   - encoding: D∗ ∈ C in Definition 1.6 → membership is included in `AdaptiveTester.IsPicky`; reason: the standing domain condition is part of the predicate, so a separate redundant hypothesis is unnecessary
--   - reading: "the following hold with probability at least 3/4" (Definitions 1.2, 1.6) → one event: the conjunction of the clauses has probability ≥ 3/4, in hypothesis and conclusion; reason: the literal reading of both definitions
--   - reading: "halfspace" (p. 1: sign(⟨w, x⟩ − t), w ∈ ℝⁿ, t ∈ ℝ) → `IsHalfspace f`: ∃ w t, ∀ x, f x = sgn(⟪w, x⟫ − t), with w = 0 (both constants) allowed; reason: p. 1 allows every w ∈ ℝⁿ; this includes both constant classifiers, including the zero-normal classifier used in Lemma 2.11
--   - reading: sign(⟨w, x⟩ − t) with sign(0) unspecified → `sgn 0 = 1` (sign(0) = +1); reason: the paper never fixes sign(0); a {±1}-valued sign needs a value there
--   - encoding: Borel f : ℝⁿ → {±1} (footnote 1) → `f : Rn n → ℝ` with `IsBoolFn f` (measurable, values ±1); reason: real values make f(x)·x and f(y)(⟨y, v⟩ − t) direct; same functions
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Proposition A.1, p. 49 (PDF 51)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Proposition A.1 (p. 49): if `A` is a `(D∗, C)`-picky halfspace tester with sample cost `m(n, ε)`
and query cost `q(n, ε)`, there is a distribution-robust halfspace tester under `{D∗}`
(Definition 1.2: guarantees for every input distribution) with sample and query cost
`O(m(n, ε) + q(n, ε))`, the `O`-constant absolute. -/
theorem proposition_A_1 :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (Dstar : ProbabilityMeasure (Rn n))
      (C : Set (ProbabilityMeasure (Rn n))),
      ∀ A : ℝ → AdaptiveTester n Bool, (∀ ε : ℝ, 0 < ε → (A ε).IsPicky Dstar C ε) →
      ∃ B : ℝ → AdaptiveTester n Verdict, ∀ ε : ℝ, 0 < ε →
        (B ε).IsRobust {Dstar} ε ∧
        ((B ε).numSamples : ℝ) ≤ K * ((A ε).numSamples + (A ε).numQueries) ∧
        ((B ε).numQueries : ℝ) ≤ K * ((A ε).numSamples + (A ε).numQueries) := by sorry

end DistRobustHalfspace.Main
