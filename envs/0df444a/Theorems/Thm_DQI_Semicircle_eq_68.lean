-- Prove2me | Theorems.Thm_DQI_Semicircle_eq_68
-- name    : DQI.Semicircle.eq_68
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:24.225623+00:00
-- url     : https://prove2.me/theorems/2d84b6d2-1dba-46a2-9950-d0030fc072b6
-- title:
--   (68), p. 26 — Σ_{|y|=k} |g̃(y)|² = C(m, k)
-- statement:
--   In the setting of §8.2.1 ($p$ prime, $|F_i|=r$ for all $i$, $1\le r\le p-1$), for every $k\ge0$,
--   $$\sum_{\mathbf y\in\mathbb F_p^m,\ |\mathbf y|=k}|\tilde g(\mathbf y)|^2=\binom mk .$$
--
--   This identity turns the norm and the quadratic form of the syndrome-space state into binomial coefficients; it is used in Lemma 9.1 and in (107)–(110).
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 26, (68)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- (68), p. 26. -/
theorem eq_68 (p : ℕ) [Fact p.Prime] (m : ℕ) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (k : ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p => wt y = k), ‖gtil F y‖ ^ 2 =
      (m.choose k : ℝ) := by sorry

end DQI.Semicircle
