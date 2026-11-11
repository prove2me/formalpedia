-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_lemma_C_2
-- name    : ApprovalCore.HarmonicEntropy.lemma_C_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:31:38.272292+00:00
-- url     : https://prove2.me/theorems/5b457ddc-e075-441e-a0ae-e23ab6420642
-- title:
--   Lemma C.2 — the truncation error satisfies $0 \le F(x) - F_L(x) \le (d-1)/L$
-- statement:
--   For every $x \in \Delta_d$ and integer $L \ge 1$,
--   $$0 \ \le\ F(x) - F_L(x) \ \le\ \frac{d-1}{L},$$
--   where $F_L(x) = \sum_{\ell=0}^{L-1}\big(\frac{1}{\ell+1} - \|\Phi^\ell(x)\|_\infty\big)$ is the truncation of the series (6). The bound is uniform in $x$, which gives continuity of $F$ from that of the partial sums and controls the error when computing committee values.
--
--   Differences from the source:
--
--   - encoding: a distribution x ∈ ∆_d with coordinates indexed by [d] → x : Fin d → ℝ with x ∈ stdSimplex ℝ (Fin d), coordinates indexed 0, …, d−1; reason: Mathlib's standard simplex is exactly ∆_d (nonnegative coordinates summing to 1); only the index base changes
--   - encoding: ∥y∥∞ → Mathlib's sup norm ‖y‖ on Fin d → ℝ; reason: the sup norm on a finite product of ℝ is max_j |y_j|, i.e. ∥y∥∞
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 33 (PDF 34), Lemma C.2

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_RobinHood

namespace ApprovalCore.HarmonicEntropy

/-- Lemma C.2 (p. 33): for every `x ∈ ∆d` and integer `L ≥ 1`,
`0 ≤ F(x) − F_L(x) ≤ (d − 1)/L`. -/
theorem lemma_C_2 {d : ℕ} (x : Fin d → ℝ) (hx : x ∈ stdSimplex ℝ (Fin d)) (L : ℕ)
    (hL : 1 ≤ L) :
    0 ≤ harmonicEntropy x - harmonicEntropyTrunc L x ∧
      harmonicEntropy x - harmonicEntropyTrunc L x ≤ ((d : ℝ) - 1) / (L : ℝ) := by sorry

end ApprovalCore.HarmonicEntropy
