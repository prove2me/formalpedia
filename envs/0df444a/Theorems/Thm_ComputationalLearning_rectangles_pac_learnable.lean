-- Prove2me | Theorems.Thm_ComputationalLearning_rectangles_pac_learnable
-- name    : ComputationalLearning.rectangles_pac_learnable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:00:19.793984+00:00
-- url     : https://prove2.me/theorems/e578a251-698e-49c9-a73f-03739460a897
-- title:
--   Theorem 1.1: axis-aligned rectangles are PAC learnable by the tightest-fit algorithm with m ≥ (4/ε) ln(4/δ) examples
-- statement:
--   **Theorem 1.1.** The concept class of axis-aligned rectangles over the Euclidean plane $\mathbb{R}^2$ is efficiently PAC learnable.
--
--   Formally (sample-complexity sense, with the book's algorithm and bound, p. 6): for every target rectangle $[a_1, b_1] \times [a_2, b_2]$, every probability measure $D$ on $\mathbb{R}^2$, $\epsilon > 0$, $0 < \delta < 1$ and $m \ge (4/\epsilon)\ln(4/\delta)$: the tightest-fit rectangle is consistent with every sample labeled by the target; the probability, under the law of $m$ independent labeled examples, that the tightest-fit rectangle has error greater than $\epsilon$ is at most $\delta$; and the class of axis-aligned rectangles is PAC learnable using axis-aligned rectangles. The distribution is arbitrary (the four-strip argument is carried out for measures with atoms by taking the strip of height $t^* = \sup\{t : \text{weight of } \{y \ge t\} \cap R \ge \epsilon/4\}$).
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §1.1 pp. 3-6 (the tightest-fit algorithm and its analysis) and Theorem 1.1, p. 12

import Definitions.Def_ComputationalLearning_PAC

open MeasureTheory

namespace ComputationalLearning

/-- **Theorem 1.1** (p. 12). The concept class of axis-aligned rectangles over the Euclidean
plane is (efficiently) PAC learnable, by the tightest-fit algorithm: for every target rectangle,
every distribution `D` on the plane and `ε, δ > 0`, the tightest-fit rectangle is consistent with
every sample labeled by the target, and with `m ≥ (4/ε) ln(4/δ)` examples it has error greater
than `ε` with probability at most `δ` (§1.1, p. 6); hence rectangles are PAC learnable using
rectangles in the sample-complexity sense. -/
theorem rectangles_pac_learnable (a b : ℝ × ℝ) (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 4 / ε * Real.log (4 / δ) ≤ m) :
    (∀ S : Fin m → (ℝ × ℝ) × Bool, IsLabeledBy (rectConcept a b) S →
      IsConsistent (tightestFit S) S) ∧
    sampleLaw D (rectConcept a b) m {S | ε < errorOf D (rectConcept a b) (tightestFit S)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable rectangleClass rectangleClass := by sorry

end ComputationalLearning
