-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_compact_second_ibp_one_dim
-- name    : AppliedSDE.SarkkaSolin.compact_second_ibp_one_dim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:25:44.215422+00:00
-- url     : https://prove2.me/theorems/3caaf11c-4e54-4187-ad69-2513a46193cd
-- title:
--   Second-order global integration by parts for C2 compact tests
-- statement:
--   For a C2 compactly supported real test function u and C2 coefficient v, integrating u times v second derivative equals integrating u second derivative times v. This is obtained by applying the one-dimensional compact first-order integration by parts twice and is needed for the diffusion term of formal Fokker Planck adjoint theorem 58d33226-7e65-415f-bf58-71b16064bec0.
-- source:
--   Sarkka and Solin (2019) Fokker Planck generator; parent 58d33226-7e65-415f-bf58-71b16064bec0.

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.compact_second_ibp_one_dim
    (u v : ℝ -> ℝ) (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (hcompact : HasCompactSupport u) :
    (∫ x : ℝ, u x * deriv (deriv v) x) =
      (∫ x : ℝ, deriv (deriv u) x * v x) := by
  sorry
