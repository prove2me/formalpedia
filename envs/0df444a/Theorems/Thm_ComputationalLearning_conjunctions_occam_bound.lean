-- Prove2me | Theorems.Thm_ComputationalLearning_conjunctions_occam_bound
-- name    : ComputationalLearning.conjunctions_occam_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:04:21.938923+00:00
-- url     : https://prove2.me/theorems/62df741a-4a8a-4d87-adcd-7b55826b976c
-- title:
--   §2.2: by Occam's Razor the elimination algorithm needs only m ≥ (1/ε)(ln(3ⁿ + 1) + ln(1/δ)) examples
-- statement:
--   **§2.2** (p. 38). The elimination algorithm always outputs a conjunction consistent with its sample, so it is an Occam algorithm; the number of conjunctions over $x_1, \dots, x_n$ is bounded by $3^n$ (each variable occurs positively or negatively or is absent), so applying Theorem 2.2, $O((1/\epsilon)\log(1/\delta) + n/\epsilon)$ examples are sufficient to guarantee that the hypothesis has error less than $\epsilon$ with confidence at least $1 - \delta$, an improvement by a logarithmic factor over Chapter 1.
--
--   Formally: for every target conjunction $T$, every distribution $D$ on $\{0,1\}^n$, $0 < \epsilon \le 1$, $\delta > 0$ and $m \ge (1/\epsilon)(\ln(3^n + 1) + \ln(1/\delta))$, the probability that the elimination hypothesis has error greater than $\epsilon$ is at most $\delta$. The count $3^n + 1$ includes the empty concept, which the elimination algorithm outputs (as a contradictory conjunction) on a sample without positive examples.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §2.2 pp. 37-38, the improved sample size for learning conjunctions

import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory

namespace ComputationalLearning

/-- **§2.2, the improved sample size for conjunctions** (pp. 37–38). The elimination algorithm is
an Occam algorithm for conjunctions, and the hypothesis class it uses has at most `3ⁿ + 1`
concepts (each variable positive, negated or absent, plus the empty concept of a contradictory
conjunction); by Theorem 2.2, `m ≥ (1/ε)(ln(3ⁿ + 1) + ln(1/δ))`, i.e.
`O((1/ε) log(1/δ) + n/ε)`, examples suffice for error at most `ε` with confidence `1 − δ`, a
logarithmic improvement over the bound of Chapter 1. -/
theorem conjunctions_occam_bound {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (m : ℕ)
    (hm : 1 / ε * (Real.log (3 ^ n + 1) + Real.log (1 / δ)) ≤ m) :
    sampleLaw D (evalConj T) m {S | ε < errorOf D (evalConj T) (evalConj (eliminate S))} ≤
      ENNReal.ofReal δ := by sorry

end ComputationalLearning
