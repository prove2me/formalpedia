-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_lemma_20
-- name    : DriftVarCtrl.FixedLB.lemma_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:39.358739+00:00
-- url     : https://prove2.me/theorems/fa6eb454-c74a-47e9-88ca-96a3aeb68513
-- title:
--   Lemma 20, p. EC-32 — xeˣ + 1 ≥ eˣ, xeˣ + x + 2 ≥ 2eˣ, x²eˣ + 2x + 2 ≥ 2eˣ for x ≥ 0
-- statement:
--   For every $x \ge 0$,
--   $$xe^x + 1 \ge e^x,\qquad xe^x + x + 2 \ge 2e^x,\qquad x^2e^x + 2x + 2 \ge 2e^x .$$
--
--   These inequalities (196)–(198) are used in the proof of Lemma 1.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-32, Appendix D, Lemma 20, (196)–(198)

import Mathlib

namespace DriftVarCtrl.FixedLB

/-- Lemma 20 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-32, (196)–(198)). For `x ≥ 0`:
`x eˣ + 1 ≥ eˣ`, `x eˣ + x + 2 ≥ 2eˣ` and `x² eˣ + 2x + 2 ≥ 2eˣ`. -/
theorem lemma_20 (x : ℝ) (hx : 0 ≤ x) :
    Real.exp x ≤ x * Real.exp x + 1 ∧
    2 * Real.exp x ≤ x * Real.exp x + x + 2 ∧
    2 * Real.exp x ≤ x ^ 2 * Real.exp x + 2 * x + 2 := by sorry

end DriftVarCtrl.FixedLB
