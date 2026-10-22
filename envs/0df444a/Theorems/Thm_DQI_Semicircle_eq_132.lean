-- Prove2me | Theorems.Thm_DQI_Semicircle_eq_132
-- name    : DQI.Semicircle.eq_132
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:23.917422+00:00
-- url     : https://prove2.me/theorems/8e25c418-b1b8-43d4-a1cc-2b874a860d63
-- title:
--   (132), p. 34 — if r/p ≤ 1 − ℓ/m then (p − 2r)/√(r(p − r)) ≥ −(m − 2ℓ)/√(ℓ(m − ℓ))
-- statement:
--   Let $1\le r<p$ and $1\le\ell<m$ be integers with $r/p\le1-\ell/m$. Then
--   $$d=\frac{p-2r}{\sqrt{r(p-r)}}\ \ge\ -\frac{m-2\ell}{\sqrt{\ell(m-\ell)}} .$$
--
--   This is the step that makes Lemma 9.3 applicable to the matrix of Lemma 9.2 in the regime $r/p\le1-\ell/m$.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 34, §9.4, (132)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- (132), p. 34: if `r/p ≤ 1 − ℓ/m` then `d ≥ −(m − 2ℓ)/√(ℓ(m − ℓ))`. -/
theorem eq_132 (p r m ℓ : ℕ) (hr : 1 ≤ r) (hrp : r < p) (hℓ : 1 ≤ ℓ) (hℓm : ℓ < m)
    (h : (r : ℝ) / p ≤ 1 - (ℓ : ℝ) / m) :
    -((m : ℝ) - 2 * ℓ) / Real.sqrt (ℓ * ((m : ℝ) - ℓ)) ≤ dparOf p r := by sorry

end DQI.Semicircle
