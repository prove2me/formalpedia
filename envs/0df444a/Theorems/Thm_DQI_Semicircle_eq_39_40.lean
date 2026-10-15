-- Prove2me | Theorems.Thm_DQI_Semicircle_eq_39_40
-- name    : DQI.Semicircle.eq_39_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:19.189251+00:00
-- url     : https://prove2.me/theorems/a1fdcc04-5630-4d1f-b933-3a82f1705c60
-- title:
--   (39)–(40), p. 21 — f̄ = 2r/p − 1, φ = √(4r(1 − r/p)), and g_i, g̃_i are normalized with g̃_i(0) = 0
-- statement:
--   Let $p$ be a prime, $F_i\subseteq\mathbb F_p$ with $|F_i|=r$ where $1\le r\le p-1$, and let $f_i=2\cdot\mathbb 1_{F_i}-1$. With $\bar f$, $\varphi$, $g_i$ and $\tilde g_i$ as in §8.2.1,
--   $$\bar f=\frac{2r}{p}-1,\qquad \varphi=\sqrt{4r\Big(1-\frac rp\Big)},$$
--   and
--   $$\sum_{x\in\mathbb F_p}|g_i(x)|^2=\sum_{y\in\mathbb F_p}|\tilde g_i(y)|^2=1,\qquad \tilde g_i(0)=0.$$
--
--   These identities make the $g_i$ a normalized, mean-zero encoding of the constraints; they are what the normalization $\sqrt{p^{n-k}\binom mk}$ of the DQI states and the counting identity (68) rest on.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 21, §8.2.1, (37)–(40)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- (39)–(40) and the normalization of §8.2.1, p. 21. -/
theorem eq_39_40 (p : ℕ) [Fact p.Prime] (m : ℕ) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (i : Fin m) :
    fbar F i = 2 * (r : ℝ) / p - 1 ∧
    phi F i = Real.sqrt (4 * r * (1 - (r : ℝ) / p)) ∧
    ∑ x : ZMod p, g F i x ^ 2 = 1 ∧
    gt F i 0 = 0 ∧
    ∑ y : ZMod p, ‖gt F i y‖ ^ 2 = 1 := by sorry

end DQI.Semicircle
