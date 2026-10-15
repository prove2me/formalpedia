-- Prove2me | Theorems.Thm_DQI_Semicircle_eq_129
-- name    : DQI.Semicircle.eq_129
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:22.118586+00:00
-- url     : https://prove2.me/theorems/ce984df6-3145-4996-b883-54ed96690f1d
-- title:
--   (129), p. 33 — if 1 ≤ ℓ ≤ m/2 and d ≥ −(m − 2ℓ)/√(ℓ(m − ℓ)), every eigenvalue of A^(m,ℓ,d) is ≤ 2√m + ℓd + 2√(ℓ(m − ℓ))
-- statement:
--   Let $m,\ell$ be integers with $1\le\ell\le m/2$ and let $d\in\mathbb R$ satisfy
--   $$d\ \ge\ -\frac{m-2\ell}{\sqrt{\ell(m-\ell)}} .$$
--   Then every real eigenvalue $\lambda$ of the tridiagonal matrix $A^{(m,\ell,d)}$ satisfies
--   $$\lambda\ \le\ 2\sqrt m+\ell d+2\sqrt{\ell(m-\ell)} .$$
--
--   This is the upper half of Lemma 9.3 at finite size.
--
--   **Formalization Note** $\ell\ge1$ is added so that the hypothesis does not divide by $\sqrt0$; the page uses this bound as $\ell\to\infty$.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 33, proof of Lemma 9.3, (123)–(129)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- (129), p. 33 (Gershgorin bound in the proof of Lemma 9.3). -/
theorem eq_129 (m ℓ : ℕ) (dpar : ℝ) (hℓ : 1 ≤ ℓ) (hℓm : 2 * ℓ ≤ m)
    (hd : -((m : ℝ) - 2 * ℓ) / Real.sqrt (ℓ * ((m : ℝ) - ℓ)) ≤ dpar) :
    ∀ t ∈ spectrum ℝ (Atri m ℓ dpar),
      t ≤ 2 * Real.sqrt m + ℓ * dpar + 2 * Real.sqrt (ℓ * ((m : ℝ) - ℓ)) := by sorry

end DQI.Semicircle
