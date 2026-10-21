-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_lemma_21
-- name    : DriftVarCtrl.FixedLB.lemma_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:39.54529+00:00
-- url     : https://prove2.me/theorems/097c3a8d-194c-466d-91e3-db535793946e
-- title:
--   Lemma 21, p. EC-32 — bounds on x/(1 − e^{−kx}) and xe^{−kx}/(1 − e^{−kx})
-- statement:
--   Let $k > 0$. Then
--   $$\frac{x}{1-e^{-kx}} > \frac1k \ (x>0),\qquad 0<\frac{x}{1-e^{-kx}}<\frac1k\ (x<0),\qquad 0<\frac{xe^{-kx}}{1-e^{-kx}}<\frac1k\ (x>0),\qquad \frac{xe^{-kx}}{1-e^{-kx}}>\frac1k\ (x<0).$$
--
--   These four elementary inequalities, (199)–(202), are used for the middle inequalities of Lemma 1, which order the slopes of Theorem 2.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-32, Appendix D, Lemma 21, (199)–(202)

import Mathlib

namespace DriftVarCtrl.FixedLB

/-- Lemma 21 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-32, (199)–(202)). For `k > 0`:
`x/(1 − e^{−kx}) > 1/k` if `x > 0`; `0 < x/(1 − e^{−kx}) < 1/k` if `x < 0`;
`0 < x e^{−kx}/(1 − e^{−kx}) < 1/k` if `x > 0`; `x e^{−kx}/(1 − e^{−kx}) > 1/k` if `x < 0`. -/
theorem lemma_21 (k : ℝ) (hk : 0 < k) :
    (∀ x : ℝ, 0 < x → 1 / k < x / (1 - Real.exp (-k * x))) ∧
    (∀ x : ℝ, x < 0 → 0 < x / (1 - Real.exp (-k * x)) ∧ x / (1 - Real.exp (-k * x)) < 1 / k) ∧
    (∀ x : ℝ, 0 < x → 0 < x * Real.exp (-k * x) / (1 - Real.exp (-k * x)) ∧
      x * Real.exp (-k * x) / (1 - Real.exp (-k * x)) < 1 / k) ∧
    (∀ x : ℝ, x < 0 → 1 / k < x * Real.exp (-k * x) / (1 - Real.exp (-k * x))) := by sorry

end DriftVarCtrl.FixedLB
