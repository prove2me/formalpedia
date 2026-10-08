-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_tilted_scale_log_concave
-- name    : AvramDividend.Classical.bv_ac_esscher_tilted_scale_log_concave
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T10:59:49.645124+00:00
-- url     : https://prove2.me/theorems/18a4a2bd-14b6-4ee9-9b26-853dd5b4410c
-- title:
--   Log-concavity of the Esscher-tilted BV scale function
-- statement:
--   Establish the log-concavity on the positive axis of V=e^(-φx)W^(q)(x) at the positive Esscher root, for a standing BV spectrally negative Lévy process with absolutely continuous jump measure. This is a substantive scale-function fluctuation theorem. It follows from the excursion-height intensity, since (log V)' is the nonincreasing excursion tail, but cannot be inferred from monotonicity of W alone.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013), §2.3, integrated excursion-height representation (2.17) and one-sided derivatives (2.18).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_ac_esscher_tilted_scale_log_concave
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, V x = Real.exp (-(φ * x)) * W x) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) := by sorry
