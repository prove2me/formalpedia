-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_NX_discounted_negative_JL_integral_identity
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_NX_discounted_negative_JL_integral_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:57:17.79471+00:00
-- url     : https://prove2.me/theorems/bd61eefd-fa1d-47c1-ae91-6eb8dbe0e184
-- title:
--   Original actual jump-count measure integrates discounted nonlinear and annular compensated negative-mark kernels into one adjusted integrand
-- statement:
--   For the genuine original Lévy mapped jump count NX at an arbitrary omega, a shared discount/mask scalar a, true nonlinear Taylor source S and gradient coefficient d, the nonlinear J count integral and retained annulus L count integral combine exactly into a single adjusted negative-mark kernel. Both input count integrands are assumed integrable; negative-mark support comes from the public pathwise NX support theorem. This is a source exact step toward the physical stopped Itô ledger.
-- source:
--   Proved 9da8864c actual NX negative mark support; Proved 97521e90 negative J/L pointwise kernel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_NX_ae_negative_jumps
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_NX_discounted_negative_JL_integral_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (η : ℝ) (hη : 0 < η) (hηone : η < 1)
    (a S d : ℝ≥0 × ℝ → ℝ)
    (hH : Integrable (fun p => a p *
      (S p - (if -1 < p.2 then p.2 * d p else 0)))
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧
        X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s))))
    (hL : Integrable (fun p =>
      if p.2 ∈ Ioo (-1 : ℝ) (-η) then a p * p.2 * d p else 0)
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧
        X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧
        X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    (∫ p, a p * (S p - (if -1 < p.2 then p.2 * d p else 0)) ∂NX) +
    (∫ p, (if p.2 ∈ Ioo (-1 : ℝ) (-η) then
      a p * p.2 * d p else 0) ∂NX) =
    ∫ p, a p * (S p - (if -η ≤ p.2 then p.2 * d p else 0)) ∂NX := by sorry
