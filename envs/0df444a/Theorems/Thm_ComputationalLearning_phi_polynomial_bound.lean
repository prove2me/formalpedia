-- Prove2me | Theorems.Thm_ComputationalLearning_phi_polynomial_bound
-- name    : ComputationalLearning.phi_polynomial_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:13:31.599984+00:00
-- url     : https://prove2.me/theorems/85859061-d317-4740-af29-52a458da9fa9
-- title:
--   The polynomial bound on Φ_d(m) (p. 57): Φ_d(m) = 2^m for m ≤ d, and Φ_d(m) ≤ (em/d)^d for m ≥ d ≥ 1
-- statement:
--   **p. 57.** For $m \le d$, $\Phi_d(m) = 2^m$. For $m > d$, since $0 \le d/m \le 1$, $\big(\tfrac{d}{m}\big)^d \Phi_d(m) \le \sum_{i=0}^{d}\binom{m}{i}\big(\tfrac{d}{m}\big)^i \le \big(1 + \tfrac{d}{m}\big)^m < e^d$, so $\Phi_d(m) \le \big(\tfrac{em}{d}\big)^d = O(m^d)$.
--
--   Formally: for all $d, m$: if $m \le d$ then $\Phi_d(m) = 2^m$; and if $1 \le d \le m$ then $\Phi_d(m) \le (em/d)^d$ (as real numbers; at $m = d$ this is $2^d \le e^d$).
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §3.4 p. 57, the bound Φ_d(m) ≤ (em/d)^d = O(m^d)

import Definitions.Def_ComputationalLearning_VC

open MeasureTheory

namespace ComputationalLearning

/-- **The polynomial bound on `Φ_d(m)`** (p. 57): for `m ≤ d`, `Φ_d(m) = 2^m`, and for `m ≥ d ≥ 1`,
`Φ_d(m) ≤ (em/d)^d = O(m^d)`. -/
theorem phi_polynomial_bound (d m : ℕ) :
    (m ≤ d → Phi d m = 2 ^ m) ∧
    (1 ≤ d → d ≤ m → (Phi d m : ℝ) ≤ (Real.exp 1 * m / d) ^ d) := by sorry

end ComputationalLearning
