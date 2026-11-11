-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_lemma_B_1
-- name    : ApprovalCore.HarmonicEntropy.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:31:09.989784+00:00
-- url     : https://prove2.me/theorems/c41524cf-18c0-48c4-b6fc-86680c7a6d95
-- title:
--   Lemma B.1 — $\Phi^{\ell+1}(x) = \Phi(\Phi^\ell(x))$ for $\ell \ge 1$
-- statement:
--   Let $x \in \Delta_d$ and let $\ell \ge 1$ be an integer. Then the Robin Hood operator with $\ell + 1$ steps equals one application of $\Phi = \Phi^1$ after the operator with $\ell$ steps:
--   $$\Phi^{\ell+1}(x) = \Phi(\Phi^\ell(x)).$$
--   Both sides are vectors on $d + \ell + 1$ coordinates whose first $d$ coordinates are the capped old ones. The lemma lets the multi-step operator, which enters the series representation of $F$, be computed by iterating the single-step one, which defines $F$.
--
--   Differences from the source:
--
--   - encoding: a distribution x ∈ ∆_d with coordinates indexed by [d] → x : Fin d → ℝ with x ∈ stdSimplex ℝ (Fin d), coordinates indexed 0, …, d−1; reason: Mathlib's standard simplex is exactly ∆_d (nonnegative coordinates summing to 1); only the index base changes
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 30 (PDF 31), Lemma B.1

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_RobinHood

namespace ApprovalCore.HarmonicEntropy

/-- Lemma B.1 (p. 30): for every `x ∈ ∆d` and integer `ℓ ≥ 1`, `Φ^{ℓ+1}(x) = Φ(Φ^ℓ(x))`
(both vectors on `d + ℓ + 1` coordinates, the new ones after the old ones). -/
theorem lemma_B_1 {d : ℕ} (x : Fin d → ℝ) (hx : x ∈ stdSimplex ℝ (Fin d)) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) :
    robinHood (ℓ + 1) x = Phi (robinHood ℓ x) := by sorry

end ApprovalCore.HarmonicEntropy
