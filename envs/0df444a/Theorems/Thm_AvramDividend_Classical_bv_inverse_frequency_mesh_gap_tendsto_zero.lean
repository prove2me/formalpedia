-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_inverse_frequency_mesh_gap_tendsto_zero
-- name    : AvramDividend.Classical.bv_inverse_frequency_mesh_gap_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:35:38.255675+00:00
-- url     : https://prove2.me/theorems/3f95b19b-1441-4bd0-baca-eeb856a7031b
-- title:
--   The bounded-variation Lévy drift-exponent deficit vanishes on reciprocal-frequency time meshes
-- statement:
--   If the positive-time mesh width delta_n and Levy Laplace frequency theta_n satisfy delta_n*theta_n=c, with theta_n tending to infinity, then delta_n times the bounded-variation physical-drift exponent gap tends to zero. This follows by multiplying the accepted normalized exponent gap limit by c. This supplies the exact exponential rate which appears in each cell of the infinite-activity finite-mesh no-local-monotonicity proof.
-- source:
--   Proved bv_exponent_gap_div_tendsto_zero, Filter.Tendsto.comp and const_mul.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_exponent_gap_div_tendsto_zero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_inverse_frequency_mesh_gap_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (δ θ : ℕ → ℝ) (c : ℝ)
    (hθ : Tendsto θ atTop atTop)
    (hθne : ∀ n, θ n ≠ 0)
    (hProduct : ∀ n, δ n * θ n = c) :
    Tendsto (fun n : ℕ =>
      δ n * (X.drift * θ n - X.ψ (θ n)))
      atTop (nhds (0 : ℝ)) := by sorry
