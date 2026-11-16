-- Prove2me | solution 1 for gauss_b_20261113_b237_pointwise_upper_bound_8ca326b5
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T15:21:44.781536+00:00
-- url     : https://prove2.me/submissions/950568c6-580c-43a4-a25b-20dd4031488e

import Mathlib
open MeasureTheory Filter Topology

noncomputable section

theorem gauss_pointwise_aux
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β)
    (f g : ℕ → α → β → ℝ)
    (hff : ∀ m p s, Integrable
      (fun ω => (f m s ω - f p s ω)^2) ν)
    (hfg : ∀ m s, Integrable
      (fun ω => (f m s ω - g m s ω)^2) ν)
    (hgg : ∀ m p s, Integrable
      (fun ω => (g m s ω - g p s ω)^2) ν) :
    ∀ (m p : ℕ) (s : α), (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ≤
        3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) +
          ((∫ ω, (g m s ω - g p s ω)^2 ∂ν) +
           (∫ ω, (f p s ω - g p s ω)^2 ∂ν))) := by
  intro m p s
  have h1 := hfg m s
  have h2 := hgg m p s
  have h3 := hfg p s
  have h23 : Integrable (fun ω => (g m s ω - g p s ω)^2 + (f p s ω - g p s ω)^2) ν := h2.add h3
  have h123 : Integrable (fun ω => (f m s ω - g m s ω)^2 +
      ((g m s ω - g p s ω)^2 + (f p s ω - g p s ω)^2)) ν := h1.add h23
  rw [← integral_add h2 h3, ← integral_add h1 h23, ← integral_const_mul]
  refine integral_mono (hff m p s) (h123.const_mul 3) ?_
  intro ω
  nlinarith [sq_nonneg ((f m s ω - g m s ω) - (g m s ω - g p s ω)),
    sq_nonneg ((f m s ω - g m s ω) - (g p s ω - f p s ω)),
    sq_nonneg ((g m s ω - g p s ω) - (g p s ω - f p s ω))]

theorem gauss_outer_aux
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (f g : ℕ → α → β → ℝ)
    (hffOuter : ∀ m p, Integrable
      (fun s => ∫ ω, (f m s ω - f p s ω)^2 ∂ν) μ)
    (hfgOuter : ∀ m, Integrable
      (fun s => ∫ ω, (f m s ω - g m s ω)^2 ∂ν) μ)
    (hggOuter : ∀ m p, Integrable
      (fun s => ∫ ω, (g m s ω - g p s ω)^2 ∂ν) μ)
    (hpt : ∀ (m p : ℕ) (s : α), (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ≤
        3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) +
          ((∫ ω, (g m s ω - g p s ω)^2 ∂ν) +
           (∫ ω, (f p s ω - g p s ω)^2 ∂ν)))) (m p : ℕ) :
    (∫ s, (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ∂μ) ≤
      3 * ((∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ) +
        ((∫ s, (∫ ω, (g m s ω - g p s ω)^2 ∂ν) ∂μ) +
        (∫ s, (∫ ω, (f p s ω - g p s ω)^2 ∂ν) ∂μ))) := by
  have h1 := hfgOuter m
  have h2 := hggOuter m p
  have h3 := hfgOuter p
  have h23 : Integrable (fun s => (∫ ω, (g m s ω - g p s ω)^2 ∂ν) +
      (∫ ω, (f p s ω - g p s ω)^2 ∂ν)) μ := h2.add h3
  have h123 : Integrable (fun s => (∫ ω, (f m s ω - g m s ω)^2 ∂ν) +
      ((∫ ω, (g m s ω - g p s ω)^2 ∂ν) + (∫ ω, (f p s ω - g p s ω)^2 ∂ν))) μ := h1.add h23
  rw [← integral_add h2 h3, ← integral_add h1 h23, ← integral_const_mul]
  exact integral_mono (hffOuter m p) (h123.const_mul 3) (fun s => hpt m p s)


theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (f g : ℕ → α → β → ℝ)
    (hff : ∀ m p s, Integrable
      (fun ω => (f m s ω - f p s ω)^2) ν)
    (hfg : ∀ m s, Integrable
      (fun ω => (f m s ω - g m s ω)^2) ν)
    (hgg : ∀ m p s, Integrable
      (fun ω => (g m s ω - g p s ω)^2) ν)
    (hffOuter : ∀ m p, Integrable
      (fun s => ∫ ω, (f m s ω - f p s ω)^2 ∂ν) μ)
    (hfgOuter : ∀ m, Integrable
      (fun s => ∫ ω, (f m s ω - g m s ω)^2 ∂ν) μ)
    (hggOuter : ∀ m p, Integrable
      (fun s => ∫ ω, (g m s ω - g p s ω)^2 ∂ν) μ)
    (hClose : Tendsto (fun m =>
      ∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)))
    (hCauchy : Tendsto (fun mp : ℕ × ℕ =>
      ∫ s, (∫ ω, (g mp.1 s ω - g mp.2 s ω)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ))) 
    (hTri : (∀ (a b c : ℝ), (a + b + c)^2 ≤ 3 * (a^2 + b^2 + c^2)))
    : (∀ (m p : ℕ), (∫ s, (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ∂μ) ≤
      3 * ((∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ) +
        (∫ s, (∫ ω, (g m s ω - g p s ω)^2 ∂ν) ∂μ) +
        (∫ s, (∫ ω, (f p s ω - g p s ω)^2 ∂ν) ∂μ))) := by
  intro m p
  have := gauss_outer_aux μ ν f g hffOuter hfgOuter hggOuter
    (gauss_pointwise_aux ν f g hff hfg hgg) m p
  linarith

end
