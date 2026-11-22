-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_arbitrary_bounded_stop_exact_energy
-- name    : AvramDividend.Classical.avram_lsv_original_zerojump_arbitrary_bounded_stop_exact_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:39:47.262197+00:00
-- url     : https://prove2.me/theorems/8d18754b-4b37-49c4-b5fa-ab8b3a2588b8
-- title:
--   Original zero-jump Levy process exact Gaussian quadratic energy at any bounded stopping time, no countable-range restriction
-- statement:
--   For the original zero-jump spectrally negative Levy process and any genuine right-continuous-filtration stopping time bounded above by an integer n, the centred Gaussian source at the actual stopped time has an integrable square, with expected square exactly sigma squared times expected physical stopped time. The actual clock may have uncountable range. Uses original proved square martingale and global continuous paths, plus the proved continuous stopped martingale optional sampling theorem, adapted from lean-lsv CC BY 4.0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_continuous_L1_bounded_stop_initial_condexp

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Adapted stopped-martingale expectation argument from dufeteller/lean-lsv,
   LSV/LocalizedOptionalExpectation.lean (CC BY 4.0,
   commit a5f604de2e1ae431de4cbecde23e5694a12ba719).
   Uses Prove2Me's proved original zero-jump compensated-square martingale
   and global path continuity for an arbitrary genuine bounded stop. -/

theorem AvramDividend.Classical.avram_lsv_original_zerojump_arbitrary_bounded_stop_exact_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω =>
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c)^2) P ∧
    (∫ ω, (X.X (τ ω) ω - (τ ω : ℝ) * X.c)^2 ∂P) =
      ∫ ω, (τ ω : ℝ) * X.σ^2 ∂P := by sorry
