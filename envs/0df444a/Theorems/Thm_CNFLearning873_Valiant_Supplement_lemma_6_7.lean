-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_Supplement_lemma_6_7
-- name    : CNFLearning873.Valiant.Supplement.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:42:41.999722+00:00
-- url     : https://prove2.me/theorems/db80a24d-5164-4eff-a877-10e47f9188ad
-- title:
--   Lemma 6.7 (used in the proof of Theorem 6.5) — simultaneous survivor violation bounds
-- statement:
--   Use the parameters $r,\ell,T$ of the oracle learner, with integers $k,d\ge3$, $0<\varepsilon,\delta<1$ and $n\ge n_0(k)\ge3$. Let $F$ be any satisfiable $(k,d)$-CNF and obtain $C'$ from $T$ independent uniform solutions by the published Valiant survivor rule. Simultaneously for every survivor, with probability at least $1-\delta/3$,
--
--   $$\Pr_{X\sim\mu_F}[X\text{ violates }c]\le\frac\varepsilon{1000\ell(\log_2n)^2}\quad(c\in C').$$
--
--   This establishes the good-learning-sample event that is fixed for the subsequent two lemmas; no local lemma hypothesis is required.
--
--   Differences from the source:
--   - encoding: Boolean assignments on a named n-variable set → assignments on Fin n, using the published CNF and nonempty uniform-solution laws; reason: variable relabeling changes no instance; output satisfiability prevents an undefined uniform law
--   - encoding: parameters fixed in the preceding algorithm paragraph → explicit ceilings for ell and T, with an existential n0(k) at least 3; reason: retains the printed parameters, all k,d at least 3 and all positive accuracy/confidence parameters below one
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Lemma 6.7, printed p.29 = 1-based PDF p.29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Supplement_OracleLearner

namespace CNFLearning873.Valiant.Supplement

/-- Lemma 6.7, p.29 = PDF p.29; includes every survivor simultaneously. -/
theorem lemma_6_7 (k : ℕ) (hk : 3 ≤ k) :
    ∃ n₀ : ℕ, 3 ≤ n₀ ∧ ∀ d : ℕ, 3 ≤ d → ∀ n : ℕ, n₀ ≤ n →
    ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∀ F : CNF n, KD F k d → ∀ h : (solutions F).Nonempty,
      1 - δ / 3 ≤ eventProb (sampleLaw F h (learningSamples n k d ε δ))
        (GoodSamples F h k (rounds n k d ε δ) ε) := by sorry

end CNFLearning873.Valiant.Supplement
