-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_compact_ibp_one_dim
-- name    : AppliedSDE.SarkkaSolin.compact_ibp_one_dim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:24:00.079245+00:00
-- url     : https://prove2.me/theorems/c16707ca-c789-429f-a5c6-0788541b1cce
-- title:
--   Global integration by parts for compactly supported C1 test functions
-- statement:
--   For a compactly supported continuously differentiable u and a continuously differentiable v on the real line, the global integral of u times v derivative equals minus the integral of u derivative times v. Integrability follows from compact support and continuity. This is a necessary reusable analytic lemma for the Fokker Planck generator formal adjoint theorem 58d33226-7e65-415f-bf58-71b16064bec0.
-- source:
--   Sarkka and Solin (2019) Fokker Planck adjoint; parent 58d33226-7e65-415f-bf58-71b16064bec0.

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.compact_ibp_one_dim
    (u v : ℝ -> ℝ) (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) (hcompact : HasCompactSupport u) :
    (∫ x : ℝ, u x * deriv v x) =
      -(∫ x : ℝ, deriv u x * v x) := by
  sorry
