-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54zz_event_restricted_zero_L1_limit_ae
-- name    : AvramDividend.Classical.avram_gbB54zz_event_restricted_zero_L1_limit_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:45:40.85435+00:00
-- url     : https://prove2.me/theorems/a97ea81b-675c-4fc4-8d61-3b83ee8f0b71
-- title:
--   L1 limit vanishes almost everywhere on an event where every approximating source mesh vanishes
-- statement:
--   For any measure μ, measurable event B, integrable candidate limit N and integrable sequence M, if every M_m is pointwise zero on B and the L1(μ) distances N-M_m tend to zero, then N=0 almost surely on B. This is an exact measure-theoretic source lemma for the B54c zero-stopping-time case and other selected Lévy cash limits, with no stochastic assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set
open scoped Topology

theorem AvramDividend.Classical.avram_gbB54zz_event_restricted_zero_L1_limit_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : Set Ω) (hB : MeasurableSet B)
    (N : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hNI : Integrable N μ) (hMI : ∀ m, Integrable (M m) μ)
    (hZero : ∀ m ω, ω ∈ B → M m ω = 0)
    (hL : Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂μ, ω ∈ B → N ω = 0 := by sorry
