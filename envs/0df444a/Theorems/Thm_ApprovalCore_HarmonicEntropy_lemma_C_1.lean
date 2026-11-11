-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_lemma_C_1
-- name    : ApprovalCore.HarmonicEntropy.lemma_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:31:23.465614+00:00
-- url     : https://prove2.me/theorems/06bb7a8b-4ae0-4467-ac16-28c837c1adf9
-- title:
--   Lemma C.1 — the series representation $F(x) = \sum_{\ell \ge 0} (\frac{1}{\ell+1} - \|\Phi^\ell(x)\|_\infty)$
-- statement:
--   For every $x \in \Delta_d$, with $\Phi^0(x) = x$,
--   $$F(x) = \sum_{\ell=0}^{\infty}\Big(\frac{1}{\ell+1} - \|\Phi^\ell(x)\|_\infty\Big). \qquad (6)$$
--   The series converges and its sum is harmonic entropy. It connects the recursive definition of $F$ to the water levels of Lemma 5.1 and is the route to continuity and concavity of $F$.
--
--   **Formalization Note.** The series is stated as `HasSum` of the terms indexed by $\ell \in \mathbb N$.
--
--   Differences from the source:
--
--   - encoding: a distribution x ∈ ∆_d with coordinates indexed by [d] → x : Fin d → ℝ with x ∈ stdSimplex ℝ (Fin d), coordinates indexed 0, …, d−1; reason: Mathlib's standard simplex is exactly ∆_d (nonnegative coordinates summing to 1); only the index base changes
--   - encoding: ∥y∥∞ → Mathlib's sup norm ‖y‖ on Fin d → ℝ; reason: the sup norm on a finite product of ℝ is max_j |y_j|, i.e. ∥y∥∞
--   - encoding: the infinite series ∑_{ℓ=0}^∞ converges to F(x) → HasSum (unconditional summation) of the terms with sum F(x); reason: the terms are nonnegative (∥Φ^ℓ(x)∥∞ ≤ 1/(ℓ+1), p. 33), and for nonnegative real terms unconditional and ordinary convergence to the same sum coincide
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 33 (PDF 34), Lemma C.1 (eq. (6), p. 10)

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_RobinHood

namespace ApprovalCore.HarmonicEntropy

/-- Lemma C.1 (p. 33): for every `x ∈ ∆d`,
`F(x) = ∑_{ℓ=0}^∞ (1/(ℓ+1) − ∥Φ^ℓ(x)∥∞)` with `Φ^0(x) = x`. -/
theorem lemma_C_1 {d : ℕ} (x : Fin d → ℝ) (hx : x ∈ stdSimplex ℝ (Fin d)) :
    HasSum (fun ℓ : ℕ => 1 / ((ℓ : ℝ) + 1) - ‖robinHood ℓ x‖) (harmonicEntropy x) := by sorry

end ApprovalCore.HarmonicEntropy
