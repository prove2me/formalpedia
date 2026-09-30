-- Prove2me | Theorems.Thm_ComputationalLearning_conjunctions_pac_learnable
-- name    : ComputationalLearning.conjunctions_pac_learnable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:01:15.852984+00:00
-- url     : https://prove2.me/theorems/b0078a82-28ef-4a3e-93e2-9a886dca6a56
-- title:
--   Theorem 1.2: conjunctions of boolean literals are PAC learnable by the elimination algorithm with m ≥ (2n/ε)(ln 2n + ln(1/δ)) examples
-- statement:
--   **Theorem 1.2.** The representation class of conjunctions of boolean literals is efficiently PAC learnable.
--
--   Formally (sample-complexity sense, with the book's algorithm and bound, p. 17): for every target conjunction $T$ over $x_1, \dots, x_n$, every distribution $D$ on $\{0,1\}^n$, $\epsilon > 0$, $0 < \delta < 1$ and
--   $$m \ge \frac{2n}{\epsilon}\Big(\ln 2n + \ln \frac{1}{\delta}\Big):$$
--   the elimination hypothesis (all literals not contradicted by a positive example of the sample) is consistent with every sample labeled by $T$; the probability, under the law of $m$ independent labeled examples from $(T, D)$, that the elimination hypothesis has error greater than $\epsilon$ is at most $\delta$; and the class of conjunctions is PAC learnable using conjunctions. The proof of p. 17: the hypothesis contains the literals of $T$ so never errs on negatives; its error is at most $\sum_{z \in h} p(z)$ with $p(z) = \Pr[c(a) = 1 \wedge z = 0 \text{ in } a]$; a bad literal ($p(z) \ge \epsilon/2n$) survives with probability at most $(1 - \epsilon/2n)^m \le e^{-\epsilon m/2n}$, and the union bound over $2n$ literals gives $2n\,e^{-\epsilon m/2n} \le \delta$.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §1.3 pp. 16-18, Theorem 1.2 with its proof (the elimination algorithm, bad literals and the union bound)

import Definitions.Def_ComputationalLearning_PAC

open MeasureTheory

namespace ComputationalLearning

/-- **Theorem 1.2** (p. 16). The representation class of conjunctions of boolean literals is
(efficiently) PAC learnable, by the elimination algorithm: for every target conjunction `T` over
`x₁, …, xₙ`, every distribution `D` on `{0,1}ⁿ` and `ε, δ > 0`, the elimination hypothesis is
consistent with every sample labeled by `T`, and with `m ≥ (2n/ε)(ln(2n) + ln(1/δ))` examples it
has error greater than `ε` with probability at most `δ` (the bound of p. 17); hence conjunctions
are PAC learnable using conjunctions in the sample-complexity sense. -/
theorem conjunctions_pac_learnable {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 2 * n / ε * (Real.log (2 * n) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalConj T) S →
      IsConsistent (evalConj (eliminate S)) S) ∧
    sampleLaw D (evalConj T) m {S | ε < errorOf D (evalConj T) (evalConj (eliminate S))} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (conjunctionClass (Fin n)) (conjunctionClass (Fin n)) := by sorry

end ComputationalLearning
