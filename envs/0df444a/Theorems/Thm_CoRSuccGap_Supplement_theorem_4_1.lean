-- Prove2me | Theorems.Thm_CoRSuccGap_Supplement_theorem_4_1
-- name    : CoRSuccGap.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:39:45.46722+00:00
-- url     : https://prove2.me/theorems/2cb7c590-f53f-4621-a479-6f8da9083730
-- title:
--   Theorem 4.1 -- test--cost theorem
-- statement:
--   Let $k\ge 1$ and fix a test system with $|\Lambda|=2^k$. If a deterministic circuit is correct at both observations of every test, then
--
--   $$
--   2^k\le \operatorname{cost}(C).
--   $$
--
--   Let one circuit be sampled from an input-independent probability distribution. If each reference or folded observation in every test is incorrect with probability at most $\varepsilon$, where $0\le\varepsilon<1/2$, then
--
--   $$
--   (1-2\varepsilon)2^k\le \mathbb E[\operatorname{cost}(C)].
--   $$
--
--   The same sampled circuit is used on both structures of a test and no independence among tests or errors is required. This is the abstract counting principle behind the later relational and matrix lower bounds.
--
--   **Formalization Note** Expected cost is a nonnegative Lebesgue integral in $\mathbb R_{\ge0}\cup\{+\infty\}$, so an infinite expectation remains infinite instead of receiving a default value. The cost random variable and both error events are explicitly required to be measurable.
--
--   Differences from the source:
--   - encoding: the source treats a circuit over the permitted operations as semantically evaluated by definition → Lean stores its reference and folded gate values and restricts to the subtype satisfying `TestCircuit.Valid`; reason: `Valid` says exactly that the stored values are obtained gate-by-gate from the labels, so this changes no circuit instance.
--   - encoding: the source writes an ordinary expectation of the finite circuit cost → Lean uses the nonnegative extended-real integral; reason: this preserves the same finite expectations and also gives the intended value for an unbounded input-independent distribution.
--   - encoding: the source uses probabilities and expectation without spelling out measurability → Lean explicitly requires the two error events and the cost random variable to be measurable; reason: these are exactly the well-posedness conditions implicit in the source's probability notation.
-- source:
--   Uezato--Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337d...), Theorem 4.1, p.24 (PDF 26)

import Definitions.Def_CoRSuccGap_Supplement_TestSystem

set_option autoImplicit false

open MeasureTheory

namespace CoRSuccGap
namespace Supplement

/-- **Theorem 4.1 (Test--cost theorem).** Uezato--Nakamura, *An Exponential Succinctness Gap
between Three-Variable Logic and the Calculus of Relations*, arXiv:2609.26778 (held version,
sha256 5ad6337d…c9b6), Theorem 4.1, p.24 (PDF 26).

For a test system with `2^k` tests, a deterministic circuit correct at the reference and folded
observation of every test has cost at least `2^k`.  For one input-independent probability
distribution of valid circuits, if each of the two observations of each test is wrong with
probability at most `ε < 1/2`, then expected cost is at least `(1-2ε)2^k`.

**Formalization Note.** The expectation is a nonnegative Lebesgue integral in `ℝ≥0∞`, avoiding the
Bochner convention that assigns zero to a nonintegrable function.  Measurability of the cost and
error events is stated explicitly.  The same measure and the same sampled circuit are used for both
observations of every test; no independence is assumed. -/
theorem theorem_4_1 (k : ℕ) (hk : 1 ≤ k) (S : TestSystem k) :
    (∀ C : TestCircuit S, C.Valid → C.Correct → 2 ^ k ≤ C.cost) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 →
      ∀ [MeasurableSpace {C : TestCircuit S // C.Valid}]
        (μ : Measure {C : TestCircuit S // C.Valid}), IsProbabilityMeasure μ →
        Measurable (fun C : {C : TestCircuit S // C.Valid} => (C.val.cost : ENNReal)) →
        (∀ lam : S.Palette,
          MeasurableSet {C : {C : TestCircuit S // C.Valid} | ¬ C.1.CorrectBase lam} ∧
          MeasurableSet {C : {C : TestCircuit S // C.Valid} | ¬ C.1.CorrectFold lam} ∧
          μ {C : {C : TestCircuit S // C.Valid} | ¬ C.1.CorrectBase lam} ≤ ENNReal.ofReal ε ∧
          μ {C : {C : TestCircuit S // C.Valid} | ¬ C.1.CorrectFold lam} ≤ ENNReal.ofReal ε) →
        ENNReal.ofReal ((1 - 2 * ε) * (2 ^ k : ℝ)) ≤
          MeasureTheory.lintegral μ
            (fun C : {C : TestCircuit S // C.Valid} => (C.val.cost : ENNReal))) := by sorry

end Supplement
end CoRSuccGap
