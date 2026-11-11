-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger66_original_clipped_finite_source_positive_integrable_of_envelope
-- name    : AvramDividend.Classical.avram_gledger66_original_clipped_finite_source_positive_integrable_of_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:58:26.840423+00:00
-- url     : https://prove2.me/theorems/79d38173-acda-475d-96b2-448ddd028399
-- title:
--   Original clipped physical source positive part is integrable from cell envelope and stopped exponential L1
-- statement:
--   A finite clipped Gaussian physical source has an integrable positive part once the source is almost-everywhere measurable, each active cell satisfies the compact-lower/exponential-upper envelope, and each stopped exponential terminal variable is integrable. The potentially arbitrarily negative source tail needs no absolute moment.
-- source:
--   Direct necessary finite-mesh integration step for original gledger53 positive-source L1; reuses Proved gledger59 cell inequality, gledger62 stopped positive exponential integrability, gledger63 compact lower, and gledger65 HJB envelope.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger59_clipped_finite_source_one_sided_upper_sum
open MeasureTheory AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gledger66_original_clipped_finite_source_positive_integrable_of_envelope
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (m : ℕ) (E Y Z : ℕ → Ω → ℝ) (w : ℝ → ℝ)
    (θ K b : ℝ) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hSmeas : AEMeasurable
      (fun ω => Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))) P)
    (hE0 : ∀ ω i, 0 ≤ E i ω)
    (hE1 : ∀ ω i, E i ω ≤ 1)
    (hcell : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
      (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
      (-b ≤ w (Y i ω) ∧
        w (Z i ω) ≤ K * Real.exp (θ * Z i ω)))
    (hexp : ∀ i ∈ Finset.range (m + 1),
      Integrable (fun ω => Real.exp (θ * Z i ω)) P) :
    Integrable (fun ω => max
      (Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))) 0) P := by sorry
