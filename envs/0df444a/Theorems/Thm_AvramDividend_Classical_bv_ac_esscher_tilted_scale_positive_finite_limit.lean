-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_tilted_scale_positive_finite_limit
-- name    : AvramDividend.Classical.bv_ac_esscher_tilted_scale_positive_finite_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T10:59:42.1918+00:00
-- url     : https://prove2.me/theorems/9c42a9e2-b6a7-4f3e-a3a4-6f03173c5338
-- title:
--   Strictly positive finite limit of the Esscher-tilted BV scale function
-- statement:
--   Under q>0 and φ=Φ(q), V(x)=e^(-φx)W^(q)(x) converges to a strictly positive finite real limit, namely 1/ψ'(φ). This statement deliberately asks only for existence of a positive finite limit and omits formalising ψ' or the exact constant. This is a distinct scale-function asymptotic theorem whose proof may use the tilted drift-to-infinity potential and a renewal/tauberian theorem.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013), asymptotic W^(q)(x)~e^(Φ(q)x)/ψ'(Φ(q)), Theorem of Scale Functions, §2-3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_ac_esscher_tilted_scale_positive_finite_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, V x = Real.exp (-(φ * x)) * W x) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (𝓝 L) := by sorry
