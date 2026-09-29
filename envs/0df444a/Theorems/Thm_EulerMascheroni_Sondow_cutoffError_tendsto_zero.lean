-- Prove2me | Theorems.Thm_EulerMascheroni_Sondow_cutoffError_tendsto_zero
-- name    : EulerMascheroni.Sondow.cutoffError_tendsto_zero
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:54:51.865408+00:00
-- url     : https://prove2.me/theorems/c6bf4441-d3be-46f0-a6b1-4343826caf49
-- title:
--   Vanishing finite-shift correction in Sondow evaluation
-- statement:
--   For every fixed nonnegative integer $n$,
--   $$\lim_{N\to\infty}E_{n,N}=0.$$
--   This records the elementary limits of the finite harmonic and logarithmic shifts in the cutoff evaluation. The case $n=0$ is included.
-- source:
--   J. Sondow, https://arxiv.org/pdf/math/0209070, v2 (2002). Finite-shift asymptotics immediately preceding equation (11), p. 8; explicit rearrangement into the defined correction.

import Definitions.Def_eulerMascheroni_sondowCutoff
open EulerMascheroni.Sondow Filter
open scoped Topology

theorem EulerMascheroni.Sondow.cutoffError_tendsto_zero (n : ℕ) :
    Tendsto (cutoffError n) atTop (𝓝 0) := by sorry
