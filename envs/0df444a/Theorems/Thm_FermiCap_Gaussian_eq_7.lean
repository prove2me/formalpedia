-- Prove2me | Theorems.Thm_FermiCap_Gaussian_eq_7
-- name    : FermiCap.Gaussian.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:03.890267+00:00
-- url     : https://prove2.me/theorems/2d2e83f4-23a7-450f-babe-2637bf572554
-- title:
--   Equation (7) — one-shot capacity from minimum output entropy
-- statement:
--   For the $n$-qubit fermionic product channel $\Phi_b$ with every attenuation $b_p\in[0,1]$, covariance and a randomizing Majorana ensemble imply
--   $$C_1(\Phi_b)=n-S_{\min}(\Phi_b).$$
--   Here $C_1$ ranges over all finite output ensembles and $S_{\min}$ ranges over all input states. This relates the unrestricted capacity to a single-state entropy optimization.
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 2, eq. (7); p. 3, §II.B

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Capacity

noncomputable section

namespace FermiCap.Gaussian

/-- Eq. (7) and §II.B: this fermionic channel is covariant, so its one-shot
Holevo capacity is the maximal output entropy minus the minimum output entropy. -/
theorem eq_7 (n : ℕ) (b : Fin (2 * n) → ℝ)
    (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1) :
    oneShotCap n (channel n b) = (n : ℝ) - minOutEntropy n (channel n b) := by sorry

end FermiCap.Gaussian
