-- Prove2me | Theorems.Thm_ContinualCounting_lemma_8_lpt21
-- name    : ContinualCounting.lemma_8_lpt21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:01.423323+00:00
-- url     : https://prove2.me/theorems/9f661694-b185-408b-a68f-abe8b171b051
-- title:
--   Lemma 8 [LPT21] — an integral inequality for non-increasing functions
-- statement:
--   Let $f:\mathbb R_+\to\mathbb R_+$ be non-increasing and let $t$ be a positive integer. Then
--   $$\int_0^\infty f(x^{1/t})^t\,dx\le\Big(\int_0^\infty f(x)\,dx\Big)^t.$$
--
--   This is the analytic core of the median-of-three bound.
--
--   Differences from the source:
--   - generalization: f : R+ → R+ → f : ℝ → ℝ≥0∞, antitone on (0, ∞); reason: the value ∞ is allowed, only the values on (0, ∞) matter, and a finite-valued f is a special case
--   - encoding: integrals over [0, ∞) → `lintegral` over `Set.Ioi 0`; reason: no integrability hypothesis is needed; both sides may be ∞, and {0} is null
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Lemma 8, p.40 (PDF p.41)

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **Lemma 8 [LPT21].** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), p.40: "Let
f : R+ → R+ be a non-increasing function and let t be a positive integer. Then
∫_{x=0}^∞ f(x^{1/t})^t dx ≤ (∫_{x=0}^∞ f(x)dx)^t."

**Formalization Note.** `f` takes values in `ℝ≥0∞` and is antitone on `(0, ∞)`; both sides are `lintegral`s
over `(0, ∞)`, so no integrability hypothesis is needed and either side may be `∞`. -/
theorem lemma_8_lpt21 (f : ℝ → ℝ≥0∞) (hf : AntitoneOn f (Set.Ioi 0)) (t : ℕ) (ht : 0 < t) :
    ∫⁻ x in Set.Ioi (0 : ℝ), f (x ^ ((1 : ℝ) / t)) ^ t ≤ (∫⁻ x in Set.Ioi (0 : ℝ), f x) ^ t := by sorry

end ContinualCounting
