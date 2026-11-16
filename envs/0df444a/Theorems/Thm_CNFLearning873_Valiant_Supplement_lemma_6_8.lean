-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_Supplement_lemma_6_8
-- name    : CNFLearning873.Valiant.Supplement.lemma_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:43:38.814217+00:00
-- url     : https://prove2.me/theorems/37e3fcb6-914c-46cc-935b-2622fd434898
-- title:
--   Lemma 6.8 (used in the proof of Theorem 6.5) — weighted-phase solution count
-- statement:
--   Let $k,d\ge3$, $0<\varepsilon,\delta<1$ and $n\ge n_0(k)\ge3$, with the oracle learner's specified sample count and round count. Fix a satisfiable $(k,d)$-CNF $F$ and learning samples that are solutions of $F$ and satisfy every survivor's violation bound from Lemma 6.7. Over only the ideal internal randomness remaining in Step 2,
--
--   $$\Pr\big[|\Omega(\widehat F)|\le2|\Omega(F)|\big]\ge1-\delta/3.$$
--
--   The statement includes Step 1's empty-survivor True return. For nonempty survivors, the formula is the best candidate actually stored by the weighted-sampling phase. The ideal samplers are untruncated here; the implementation's separate abort budget is included by Theorem 6.5.
--
--   Differences from the source:
--   - encoding: Boolean assignments on a named n-variable set → assignments on Fin n, using the published CNF and nonempty uniform-solution laws; reason: variable relabeling changes no instance; output satisfiability prevents an undefined uniform law
--   - encoding: condition on the good event and fix learning samples before Lemma 6.8 → solution-valued fixed sample sequence and GoodSamples hypotheses, with the actual ideal phase law; reason: makes the inherited p.29 context explicit; no new restriction on the source executions
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Lemma 6.8, printed p.29 = 1-based PDF p.29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Supplement_OracleLearner

namespace CNFLearning873.Valiant.Supplement

/-- Lemma 6.8, pp.29-30 = PDF pp.29-30. The p.29 conditioning paragraph is explicit;
probability is over the ideal remaining internal samplers, with the learning samples fixed. -/
theorem lemma_6_8 (k : ℕ) (hk : 3 ≤ k) :
    ∃ n₀ : ℕ, 3 ≤ n₀ ∧ ∀ d : ℕ, 3 ≤ d → ∀ n : ℕ, n₀ ≤ n →
    ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∀ F : CNF n, KD F k d → ∀ h : (solutions F).Nonempty,
    ∀ xs : Fin (learningSamples n k d ε δ) → Assignment n,
      (∀ i, xs i ∈ solutions F) → GoodSamples F h k (rounds n k d ε δ) ε xs →
      1 - δ / 3 ≤ probability (ideal (phase2 k d ε δ xs))
        (fun st => (solutions (phaseFormula st)).card ≤ 2 * (solutions F).card) := by sorry

end CNFLearning873.Valiant.Supplement
