-- Prove2me | Theorems.Thm_FD1D_DyadicMass_uniformArrivalMass_piecewiseCDF
-- name    : FD1D.DyadicMass.uniformArrivalMass_piecewiseCDF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:31.526298+00:00
-- url     : https://prove2.me/theorems/c2fc9dc8-18c6-4d6b-bfee-4bc313f4b243
-- title:
--   Dyadic Mass: uniform Arrival Mass piecewise CDF
-- statement:
--   The Dyadic Mass construction uses the uniform Arrival Mass piecewise CDF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/UniformArrival.lean#L94-L99
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/UniformArrival.lean#L94-L99

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_UniformArrival
set_option autoImplicit true
open FD1D
noncomputable section
open Set MeasureTheory
open FD1D.DyadicMass

theorem FD1D.DyadicMass.uniformArrivalMass_piecewiseCDF
    (L : ℕ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    (uniformArrivalMass L).piecewiseCDF z = z := by sorry
