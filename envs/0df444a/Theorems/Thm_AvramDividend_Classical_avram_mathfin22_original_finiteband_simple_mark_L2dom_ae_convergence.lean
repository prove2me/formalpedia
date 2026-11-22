-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_finiteband_simple_mark_L2dom_ae_convergence
-- name    : AvramDividend.Classical.avram_mathfin22_original_finiteband_simple_mark_L2dom_ae_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:09:54.189797+00:00
-- url     : https://prove2.me/theorems/379fa495-c319-449a-99ff-467080b3c7c2
-- title:
--   Original arbitrary-activity finite-band bounded simple mark integrals admit L2 physical-count domination and almost-sure convergence
-- statement:
--   Adapt the accepted physical simple-mark convergence proof 6bb2d2ba to the actual original X on a fixed finite negative-mark annulus B, eliminating its globally-finite negative activity hypothesis. The physical annulus count N is L1 by the original Campbell theorem, and its centred second moment is L2 by the original annulus count variance theorem. The proved count-to-mark L2 domination bridge supplies Integrable N². On each original path, all marks in B are bounded above by the b-cutoff, whose jump count is finite by the original cadlag separation theorem. Thus the existing finite-measure simple-mark integral bound and dominated simple-mark integral convergence apply pointwise, giving a uniform L2 envelope and a.e. convergence to the actual physical weighted jump integral. This is the original infinite-activity-compatible deterministic approximation input to the missing exact mark variance theorem 16f22886, without constructing or assuming a synthetic PoissonRandomMeasure. No local Lean/Lake.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_simple_mark_integrals_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_negative_band_count_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_workerB_original_reciprocal_band_count_L1_Campbell_20261122
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_count_to_mark_L2_transfer
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_original_finiteband_simple_mark_L2dom_ae_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (a b : ℕ) (hab : a ≤ b)
    (g : ℝ → ℝ) (f : ℕ → SimpleFunc ℝ ℝ)
    (hfBound : ∀ k z, z ∈
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1))) →
      |f k z| ≤ 1)
    (hfLimit : ∀ z ∈
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1))),
      Tendsto (fun k => f k z) atTop (𝓝 (g z))) :
    let B : Set ℝ :=
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let F : ℕ → Ω → ℝ := fun k ω =>
      ∫ p in (Ioc 0 T ×ˢ B), f k p.2 ∂NX ω
    let J : Ω → ℝ := fun ω =>
      ∫ p in (Ioc 0 T ×ˢ B), g p.2 ∂NX ω
    let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal
    Integrable N P ∧ Integrable (fun ω => (N ω)^2) P ∧
      (∀ᵐ ω ∂P, ∀ k, |F k ω| ≤ N ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (J ω))) := by sorry
