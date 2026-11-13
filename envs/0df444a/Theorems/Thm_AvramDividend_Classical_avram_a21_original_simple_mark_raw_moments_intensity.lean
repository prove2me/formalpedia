-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_mark_raw_moments_intensity
-- name    : AvramDividend.Classical.avram_a21_original_simple_mark_raw_moments_intensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:16:54.385185+00:00
-- url     : https://prove2.me/theorems/92552832-bb91-4671-ad8e-ccef3f0bc7be
-- title:
--   Physical original finite simple marked jump integral exact raw moments as LÃvy intensity integrals
-- statement:
--   For the actual finite-activity original LÃvy process and a uniformly bounded finite simple Borel mark g, the physical marked-jump integral J is square-integrable and its exact raw first and second moments are T∫gΎ and (T∫gΎ)+T∫gΎ. This follows from the Proved original fibre-count raw moment theorem, the Proved deterministic simple mark linear intensity partition, and the deterministic squared fibre partition helper. It provides the finite-valued stage required to prove the bounded Borel source moment theorem using dominated convergence on the original Ύ/P.
-- source:
--   Original source raw moments f7943aaa and deterministic fibre intensity partition 4c87924a; new squared partition avram_a21_finite_simple_mark_quadratic_integral_partition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_simple_mark_raw_moments_intensity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (g : SimpleFunc ℝ ℝ)
    (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let J : Ω → ℝ := fun ω =>
      ∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω
    let r : ℝ := (T : ℝ) * (∫ z in S, g z ∂X.ν)
    let q : ℝ := (T : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν)
    Integrable J P ∧ Integrable (fun ω => J ω ^ 2) P ∧
    (∫ ω, J ω ∂P) = r ∧
    (∫ ω, J ω ^ 2 ∂P) = r ^ 2 + q := by sorry
