-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_Supplement_lemma_6_9
-- name    : CNFLearning873.Valiant.Supplement.lemma_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:44:07.399635+00:00
-- url     : https://prove2.me/theorems/f6756bfe-319b-40eb-b518-72bee300312e
-- title:
--   Lemma 6.9 (used in the proof of Theorem 6.5) — greedy-phase TV error
-- statement:
--   Under the parameters and fixed good learning samples of Lemma 6.8, consider any reachable completed ideal Step 2 execution whose stored hypothesis has at most twice the target's solution count. Every completed greedy phase then returns a satisfiable formula satisfying
--
--   $$d_{\mathrm{TV}}(\mu_F,\mu_{\widehat F})\le\varepsilon.$$
--
--   Reachability means the state is in the support of the actual weighted-phase law, and the greedy result comes from its actual deterministic count-minimizing program. This makes explicit the source's execution context, rather than asserting the result for an arbitrary multiset or unrelated state. General TV is used: the output and target supports need not be nested. This is the final deterministic correctness implication for Theorem 6.5.
--
--   Differences from the source:
--   - encoding: Boolean assignments on a named n-variable set → assignments on Fin n, using the published CNF and nonempty uniform-solution laws; reason: variable relabeling changes no instance; output satisfiability prevents an undefined uniform law
--   - encoding: a completed algorithm execution under the p.29 conditioning paragraph → fixed good samples and supported weighted/greedy states; reason: reachability encodes the source algorithm state rather than assuming the desired conclusion; the factor-two premise is exactly the printed antecedent
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Lemma 6.9, printed p.30 = 1-based PDF p.30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Supplement_OracleLearner

namespace CNFLearning873.Valiant.Supplement

/-- Lemma 6.9, p.30 = PDF p.30, for every reachable completed ideal execution under
the inherited good-learning-sample event. General TV is used; the supports need not be nested. -/
theorem lemma_6_9 (k : ℕ) (hk : 3 ≤ k) :
    ∃ n₀ : ℕ, 3 ≤ n₀ ∧ ∀ d : ℕ, 3 ≤ d → ∀ n : ℕ, n₀ ≤ n →
    ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∀ F : CNF n, KD F k d → ∀ h : (solutions F).Nonempty,
    ∀ xs : Fin (learningSamples n k d ε δ) → Assignment n,
      (∀ i, xs i ∈ solutions F) → GoodSamples F h k (rounds n k d ε δ) ε xs →
    ∀ st : WeightedState n, ideal (phase2 k d ε δ xs) st ≠ 0 →
      (solutions (phaseFormula st)).card ≤ 2 * (solutions F).card →
    ∀ G : CNF n,
      ideal (greedyPhase (output k xs) st.best (rounds n k d ε δ) ∅) G ≠ 0 →
      GoodOutput F h ε (phaseFormula st ∪ G) := by sorry

end CNFLearning873.Valiant.Supplement
