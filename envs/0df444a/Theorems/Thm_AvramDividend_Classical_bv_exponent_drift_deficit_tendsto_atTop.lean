-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_exponent_drift_deficit_tendsto_atTop
-- name    : AvramDividend.Classical.bv_exponent_drift_deficit_tendsto_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:36:28.281051+00:00
-- url     : https://prove2.me/theorems/0ba3e9a1-92c3-46d0-a447-358683c3b8c1
-- title:
--   Infinite negative activity drives the canonical bounded-variation Lévy exponent drift deficit to infinity
-- statement:
--   For the actual canonical bounded-variation spectrally negative Lévy process, infinite negative jump intensity forces drift·n−ψ(n) to diverge along natural n. The accepted exact BV exponent identity identifies this quantity with a negative-jump exponential real integral for n≥1. BV integrability controls each such integral. The accepted restricted-real-integral divergence theorem supplies the limit. This is the process-level exponent asymptotic feeding the zero-scale right derivative argument.
-- source:
--   Lévy–Khintchine asymptotics and scale-function origin regularity in Kuznetsov Kyprianou Rivero, Theory of Scale Functions, and Avram Palmowski Pistorius (2007), https://arxiv.org/pdf/math/0702893

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Measure.Restrict

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Infinite BV jump activity makes the drift-minus-exponent deficit diverge. -/
theorem bv_exponent_drift_deficit_tendsto_atTop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤) :
    Tendsto (fun n : ℕ => X.drift * (n : ℝ) - X.ψ (n : ℝ))
      atTop atTop := by sorry

end AvramDividend.Classical
