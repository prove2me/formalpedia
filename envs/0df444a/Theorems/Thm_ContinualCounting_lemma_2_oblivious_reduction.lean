-- Prove2me | Theorems.Thm_ContinualCounting_lemma_2_oblivious_reduction
-- name    : ContinualCounting.lemma_2_oblivious_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:04.513602+00:00
-- url     : https://prove2.me/theorems/8bb9dbb7-b204-4dc2-b06f-f4aeaac7df0d
-- title:
--   Lemma 2 — reduction to oblivious noise
-- statement:
--   Let $\varepsilon>0$, $\delta\in[0,1)$, $0<\delta'<1$, and let $M$ be an $(\varepsilon,\delta)$-DP mechanism (possibly with data dependent noise) for prefix sums on inputs in $\{0,1\}^n$. Put
--   $$m=\Big\lfloor\frac{n}{2\lceil\ln(1/\delta')/\varepsilon\rceil}\Big\rfloor.$$
--   Then there is a law $\nu$ on $\mathbb R^m$ such that the oblivious mechanism $M'(x)=A^{(m)}x+z$, $z\sim\nu$, on $\{0,1\}^m$ is $(2\varepsilon,e^{\varepsilon}\delta+\delta')$-DP and
--   $$\max_{x\in\{0,1\}^m}\mathbb E\|M'(x)-A^{(m)}x\|_\infty\le\mathrm{err}_\infty(M).$$
--
--   This reduction lets the rest of the proof work with additive noise independent of the input, at a constant-factor loss in $\varepsilon$ and a polynomial loss in $n$.
--
--   Differences from the source:
--   - encoding: an oblivious mechanism M′(x) = Ax + z with z independent of x → a probability measure ν on Fin m → ℝ and `oblivious ν`; reason: the same object as a family of laws
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Lemma 2, p.17 (PDF p.18); proof App. A, pp.38–40 (PDF pp.39–41)

import Mathlib
import Definitions.Def_ContinualCounting_IsDP
import Definitions.Def_ContinualCounting_linfError
import Definitions.Def_ContinualCounting_oblivious

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **Lemma 2 (reduction to oblivious noise).** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256
986e6426…), p.17: "If there is an (ε, δ)-DP mechanism M (possibly with data dependent noise) for prefix
sums on inputs x ∈ {0, 1}^n with err∞(M) = max_{x∈{0,1}^n} E[∥M(x) − Ax∥∞], then for any choice of
0 < δ′ < 1, there is a (2ε, e^ε δ + δ′)-DP mechanism M′ with oblivious noise for prefix sums on inputs
x ∈ {0, 1}^m with m = ⌊n / (2⌈ln(1/δ′)/ε⌉)⌋ and max_{x∈{0,1}^m} E[∥M′(x) − Ax∥∞] ≤ err∞(M)."

**Formalization Note.** `n / …` is natural-number floor division. `δ′ < 1` gives `ln(1/δ′) > 0`, so the
ceiling is at least `1`. `m = 0` is allowed. -/
theorem lemma_2_oblivious_reduction {n : ℕ} (ε δ δ' : ℝ) (hε : 0 < ε) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ'0 : 0 < δ') (hδ'1 : δ' < 1) (M : (Fin n → Bool) → Measure (Fin n → ℝ))
    (hM : ∀ x, IsProbabilityMeasure (M x)) (hDP : IsDP M ε δ) :
    ∃ ν : Measure (Fin (n / (2 * ⌈Real.log (1 / δ') / ε⌉₊)) → ℝ), IsProbabilityMeasure ν ∧
      IsDP (oblivious ν) (2 * ε) (Real.exp ε * δ + δ') ∧
      linfError (oblivious ν) ≤ linfError M := by sorry

end ContinualCounting
