-- Prove2me | Theorems.Thm_BoydADMM_Prox_softThreshold_eq_shrink
-- name    : BoydADMM.Prox.softThreshold_eq_shrink
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:53.264608+00:00
-- url     : https://prove2.me/theorems/9247e45c-0d31-497c-964d-a230d835ef7a
-- title:
--   (4.2), p. 32 — S_κ(a) = (1 − κ/|a|)₊ a for a ≠ 0
-- statement:
--   For $\kappa\ge0$ and every $a\ne0$,
--   $$S_\kappa(a)=\Bigl(1-\frac{\kappa}{|a|}\Bigr)_+a.\tag{4.2}$$
--
--   This formula shows that soft thresholding is a shrinkage operator: it multiplies $a$ by a factor in $[0,1)$, moving it toward zero.
--
--   **Formalization Note** The hypothesis $a\ne0$ is the book's ("for $a\ne0$"); it is kept explicitly rather than relying on Lean's convention $\kappa/0=0$. The hypothesis $\kappa\ge0$ is implicit in the book ($\kappa=\lambda/\rho>0$) and is stated.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 32, §4.4.3, (4.2)

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem softThreshold_eq_shrink (κ : ℝ) (hκ : 0 ≤ κ) (a : ℝ) (ha : a ≠ 0) :
    softThreshold κ a = max (1 - κ / |a|) 0 * a := by sorry

end BoydADMM.Prox
