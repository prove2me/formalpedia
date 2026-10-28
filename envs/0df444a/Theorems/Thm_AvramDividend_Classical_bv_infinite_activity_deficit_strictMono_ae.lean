-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_strictMono_ae
-- name    : AvramDividend.Classical.bv_infinite_activity_deficit_strictMono_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:07:01.487997+00:00
-- url     : https://prove2.me/theorems/bd673f28-ceef-4c47-98a4-95493de4df18
-- title:
--   The drift deficit of the actual infinite-activity bounded-variation Lévy process is strictly increasing on all positive-length intervals almost surely
-- statement:
--   For a BV spectrally negative Lévy process with infinite negative Lévy measure, the physical-drift deficit dt-Xt is almost surely strictly increasing as a function of all nonnegative real times. Instantiate the already proved dense-grid strict monotonicity theorem using Mathlib's canonical countable dense sequence of NNReal values.
-- source:
--   Accepted conditional dense-grid strict monotonicity theorem; TopologicalSpace.denseRange_denseSeq in pinned Mathlib.Topology.Bases.

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_strictMono_of_dense_grid
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.NNReal.Lemmas

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_infinite_activity_deficit_strictMono_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ᵐ ω ∂P, StrictMono
      (fun t : ℝ≥0 => X.drift * (t : ℝ) - X.X t ω) := by sorry
