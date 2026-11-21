-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_physical_martingale_Taylor_cash_three_channel_uniform_L2_assembly
-- name    : AvramDividend.Classical.avram_pj_original_physical_martingale_Taylor_cash_three_channel_uniform_L2_assembly
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:35:45.793236+00:00
-- url     : https://prove2.me/theorems/b646907d-e072-4298-95da-e967c4ddef8e
-- title:
--   Uniform original physical Itô mesh residual L2 certificate from three genuine integrable components: negative-mark martingale, Taylor tail and dividend correction
-- statement:
--   Let M_k, R_k and S_k be the measurable real-valued components of the original stopped physical-grid source: compensated marked martingale, nonlinear Taylor/negative-mark error and dividend/Stieltjes-contact correction. If their individual squares are integrable and expected squares uniformly bounded by A, B and C respectively, then the actual full signed source E_k=M_k+R_k+S_k has integrable square and a uniform second-moment envelope 3(A+B+C) for every refinement. The identity follows from exact pointwise three-term quadratic Cauchy inequality, integrable domination and linearity of original expectation. This is a sound interface for the remaining physical controlled Itô source c2a65023.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_physical_martingale_Taylor_cash_three_channel_uniform_L2_assembly
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (M R S : ℕ → Ω → ℝ)
    (hM : ∀ k, Measurable (M k))
    (hR : ∀ k, Measurable (R k))
    (hS : ∀ k, Measurable (S k))
    (hMI : ∀ k, Integrable (fun ω => (M k ω)^2) P)
    (hRI : ∀ k, Integrable (fun ω => (R k ω)^2) P)
    (hSI : ∀ k, Integrable (fun ω => (S k ω)^2) P)
    (A B C : ℝ)
    (hA : ∀ k, (∫ ω, (M k ω)^2 ∂P) ≤ A)
    (hB : ∀ k, (∫ ω, (R k ω)^2 ∂P) ≤ B)
    (hC : ∀ k, (∫ ω, (S k ω)^2 ∂P) ≤ C) :
    ∀ k,
      Integrable (fun ω =>
        (|M k ω + R k ω + S k ω|)^2) P ∧
      (∫ ω, (|M k ω + R k ω + S k ω|)^2 ∂P) ≤
        3 * (A + B + C) := by sorry
