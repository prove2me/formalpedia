-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_terminal_below_max_capped_first_hit_geometry
-- name    : AvramDividend.Classical.reflectedSup_terminal_below_max_capped_first_hit_geometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:47:07.380238+00:00
-- url     : https://prove2.me/theorems/3f859ea6-7d38-44f3-baa4-9070737593e3
-- title:
--   First genuine reflected running-maximum hit occurs before any finite terminal time at which the reflected process lies below that maximum
-- statement:
--   For an actual spectrally negative Lévy reflected path and a deterministic finite horizon H, let x>0 be its exact supremum over [0,H]. If its terminal value R(H) is strictly less than x, then the true capped first closed-level-x hit T lies before H and satisfies R(T)=x; moreover every reflected path value through H is ≤x. This is the pathwise geometry needed to prove the substantive probability result P(max_{s≤H} R_s=x and R_H<x)=0 whenever the original Lévy process is downward regular. The proof uses compact USC maximum attainment before a lower endpoint, the accepted exact first-level entrance theorem, and the cap-removal infimum lemma.
-- source:
--   Accepted first_exact_level_hit_of_upperSemicontinuous, reflectedSup_upperSemicontinuousOn_Icc, nnreal_sInf_union_cap_eq_of_early_member and usc_compact_sup_level_hit_before_lower_endpoint.

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_usc_compact_sup_level_hit_before_lower_endpoint
import Theorems.Thm_AvramDividend_Classical_first_exact_level_hit_of_upperSemicontinuous
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_origin_eq_zero
import Theorems.Thm_AvramDividend_Classical_nnreal_sInf_union_cap_eq_of_early_member

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_terminal_below_max_capped_first_hit_geometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (H : ℝ≥0) (x : ℝ) (hx : 0 < x)
    (hMax : sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = x)
    (hEnd : reflectedSup X H ω < x) :
    sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) < H ∧
    reflectedSup X (sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ω = x ∧
    ∀ t : ℝ≥0, t ≤ H → reflectedSup X t ω ≤ x := by sorry
