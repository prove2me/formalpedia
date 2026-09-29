-- Prove2me | Theorems.Thm_EulerMascheroni_Sondow_remainder_tendsto_zero
-- name    : EulerMascheroni.Sondow.remainder_tendsto_zero
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:54:49.402241+00:00
-- url     : https://prove2.me/theorems/fd0d6179-45fd-43aa-819e-5e803fd80c1d
-- title:
--   Vanishing of the Sondow geometric-series remainder
-- statement:
--   For each fixed positive integer $n$,
--   $$\lim_{N\to\infty}R_{n,N}=0.$$
--   This justifies removing the geometric-series cutoff in the double integral.
-- source:
--   J. Sondow, https://arxiv.org/pdf/math/0209070, v2 (2002). Equation (9), p. 7, and the vanishing-remainder argument, p. 9.

import Definitions.Def_eulerMascheroni_sondowCutoff
open EulerMascheroni.Sondow Filter
open scoped Topology

theorem EulerMascheroni.Sondow.remainder_tendsto_zero (n : ℕ) (hn : 0 < n) :
    Tendsto (remainder n) atTop (𝓝 0) := by sorry
