-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_kappa_ar1
-- name    : Aggmetrics.DataStream.kappa_ar1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:31:35.401989+00:00
-- url     : https://prove2.me/theorems/328b10e8-4b8e-4f83-8fec-ca6547612129
-- title:
--   Data Stream: kappa ar1
-- statement:
--   `AR(1)` autocorrelation `ρ_d = r^d`: `κ = (1 + αr)/(1 - αr)`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L256-L274
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L256-L274

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.kappa_ar1 {α r : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (hr : |r| < 1) :
    kappaFactor (fun d => r ^ d) α = (1 + α * r) / (1 - α * r) := by sorry
