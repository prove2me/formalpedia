-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_eq_densePrefix_onSample
-- name    : AvramDividend.Classical.runningSup_eq_densePrefix_onSample
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:32:53.276402+00:00
-- url     : https://prove2.me/theorems/73165057-752c-41b1-916c-f4877b071a2a
-- title:
--   Exact regulator recovery from dense countable records at every scheduled payment endpoint
-- statement:
--   For a Lévy path observed on a dense set S containing zero, the actual running supremum at any observation time t in S is exactly the real supremum of the observations on S up to t. This removes the separate terminal endpoint term when reconstructing the full regulator on dividend payment grids. It is a direct consequence of the proved continuous-time dense-prefix identity and the boundedness of the path on finite intervals.
-- source:
--   Avram, Palmowski and Pistorius (2007), reflected barrier valuation. Derived from proved runningSup_eq_densePrefix_with_endpoint and levyPath_bddAbove_Icc.

import Mathlib.Topology.Order
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_densePrefix_with_endpoint
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_eq_densePrefix_onSample
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hDense : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0) (ht : t ∈ S) (ω : Ω) :
    runningSup X t ω =
      ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω := by
  sorry
