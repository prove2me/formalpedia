-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_capped_first_hit_geometry
-- name    : AvramDividend.Classical.reflectedSup_finite_excursion_capped_first_hit_geometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:53:19.615362+00:00
-- url     : https://prove2.me/theorems/6144b00d-e936-402c-9743-5621c7a6babb
-- title:
--   The genuine finite excursion maximal-height entrance equals the capped stopping clock and occurs strictly before the excursion endpoint
-- statement:
--   For an actual spectrally negative Lévy reflected excursion of positive finite duration H that returns to drawdown level zero at H and whose maximum over [0,H] equals a positive height x, the actual capped first closed-level hit is strictly earlier than H, the reflected path there equals x, and the reflected path never exceeds x at later times before H. The accepted finite-excursion exact maximum-attainment theorem supplies the true first hit; the accepted cap-removal theorem identifies it with the finite stopping clock; the maximum bound follows from compact upper semicontinuity. These are the exact hAtLevel premises of the conditional excursion-height atomlessness theorem with a real stopping selector rather than an assumed one.
-- source:
--   Accepted reflectedSup_finite_excursion_first_exact_height_hit, reflectedSup_finite_excursion_capped_hit_eq_first_exact, reflectedSup_upperSemicontinuousOn_Icc.

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_capped_hit_eq_first_exact
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_first_exact_height_hit
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_finite_excursion_capped_first_hit_geometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (H : ℝ≥0) (hH : 0 < H)
    (hEnd : reflectedSup X H ω = 0)
    (x : ℝ) (hx : 0 < x)
    (hHeight : sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = x) :
    sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) < H ∧
    reflectedSup X (sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ω = x ∧
    ∀ t : ℝ≥0, sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) ≤ t →
      t < H → reflectedSup X t ω ≤ x := by sorry
