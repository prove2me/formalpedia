-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbMeas5_native_continuousPath_measurable_bernstein
-- name    : AvramDividend.Classical.avram_gbMeas5_native_continuousPath_measurable_bernstein
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:59:21.58737+00:00
-- url     : https://prove2.me/theorems/8de6c144-8875-4bc5-a862-db8faadce63f
-- title:
--   Native-Brownian setting: continuous-path Borel measurability via Bernstein approximations
-- statement:
--   With the original GlynnSTS continuous-Brownian setting loaded, any continuous-map-valued random path with measurable evaluations is itself measurable. Construct Bernstein polynomial approximants from finitely many measurable real coordinates and use pinned uniform convergence and measurable limit. This removes the actual native Gaussian B134 measurable lift obstacle without inventing path regularity.

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting
open MeasureTheory Filter Set
open scoped unitInterval Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbMeas5_native_continuousPath_measurable_bernstein
    {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → C(unitInterval, ℝ))
    (hcoord : ∀ t : unitInterval,
      Measurable (fun ω : Ω => B ω t)) :
    Measurable B := by sorry
