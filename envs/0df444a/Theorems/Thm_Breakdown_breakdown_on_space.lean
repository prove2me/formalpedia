-- Prove2me | Theorems.Thm_Breakdown_breakdown_on_space
-- name    : Breakdown.breakdown_on_space
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T18:49:36.892786+00:00
-- url     : https://prove2.me/theorems/773beff2-994b-4d0d-ae75-8b93792297cc
-- title:
--   Theorem 1.1 (formal) — breakdown on $\mathbb R^3$ from a self-similar profile
-- statement:
--   Formal counterpart of Alpöge–Buckmaster Theorem 1.1 on $\mathbb R^3$. If a nonzero smooth self-similar profile exists (`PeriodicSimilarityProfileExists`), then for every viscosity $\nu>0$ there is smooth, compactly supported, divergence-free initial data on $\mathbb R^3$ admitting no solution smooth on $[0,\infty)\times\mathbb R^3$ with bounded energy (`BreakdownOnSpace`). The formal hypothesis asks $\|\nabla^j W\|\le C(1+\|y\|)^{-1-j}$ for $j=0,1,2$ and $\|\nabla q\|\le C(1+\|y\|)^{-3}$ (stronger than the paper's (1.3), justified by Remark 1.2 and standard pressure estimates). The formal conclusion records non-existence of a global smooth bounded-energy solution; it omits the blow-up rate $(T-t)^{-1/4}$ and convergence to the profile that the paper states.
-- source:
--   Alpöge–Buckmaster, Finite-time blow-up for the Navier–Stokes equations (20 Nov 2026), https://github.com/tristanbuckmaster/navier-stokes, lean/Challenge.lean, theorem breakdown_on_space; paper Theorem 1.1.

import Mathlib
import Definitions.Def_NSBlowupChallenge

namespace Breakdown
theorem breakdown_on_space (h : PeriodicSimilarityProfileExists) : BreakdownOnSpace := by
  sorry
end Breakdown
