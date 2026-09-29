-- Prove2me | Theorems.Thm_Esgk_parabola_sqDist_inj
-- name    : Esgk.parabola_sqDist_inj
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-16T22:57:59.478738+00:00
-- url     : https://prove2.me/theorems/1dcbfbc6-1dac-4029-9bbc-9da088671ce9
-- title:
--   Integer parabola points have pairwise distinct distances
-- statement:
--   For $b < a$ and $d < c$ in $\mathbb{N}$, if $(a-b)^2(1+(a+b)^2) = (c-d)^2(1+(c+d)^2)$ then $a = c$ and $b = d$. Hence distinct nonnegative integer points $(t,t^2)$ have pairwise distinct distances: an $n$-point set of this form is in general position and determines exactly $\binom{n}{2}$ distances. Supporting construction fact for exact distinct-distance bounds; proves no lower bound by itself.
-- source:
--   esgk-on3 lean/Esgk/Parabola.lean (Esgk.parabola_sqDist_inj), kernel-checked 2026-09-16; skeptic audit docs/skeptic-parabola-sqdist-2026-09-16.md

import Mathlib

namespace Esgk

theorem parabola_sqDist_inj {a b c d : ℕ} (hab : b < a) (hcd : d < c) : (a - b) ^ 2 * (1 + (a + b) ^ 2) = (c - d) ^ 2 * (1 + (c + d) ^ 2) → a = c ∧ b = d := by sorry

end Esgk
