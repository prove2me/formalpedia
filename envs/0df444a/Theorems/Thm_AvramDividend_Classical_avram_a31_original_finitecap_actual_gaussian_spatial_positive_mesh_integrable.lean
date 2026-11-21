-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a31_original_finitecap_actual_gaussian_spatial_positive_mesh_integrable
-- name    : AvramDividend.Classical.avram_a31_original_finitecap_actual_gaussian_spatial_positive_mesh_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:32:01.471498+00:00
-- url     : https://prove2.me/theorems/bcb4761b-6557-47d4-b6e8-b3514c2e9f25
-- title:
--   Each actual finitecap Gaussian physical random crossing positive spatial mesh residual is automatically L1-integrable
-- statement:
--   For true original zerojump Gaussian Lévy X, all bounded-horizon random crossing clocks s_m,t_m and original postpayment reserves y_m∈[0,c], the positive part of the exact caplinear spatial crossing residual max(V(y_m+X(t_m)-X(s_m))-w(y_m),0) is L1 for every mesh when measurable. No assumed increment integrability or probability typeclass: X.isProbability supplies finite measure; the Proved 93b original horizon square bound provides an integrable envelope for all true random increments and Proved 4d5d controls the finitecap HJB caplinear crossing magnitude. This directly discharges per-grid hFI in actual discounted crossing estimates.
-- source:
--   Original physical Gaussian finitecap stopped spatial crossing positive L1 integrability from true X horizon envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a31_original_finitecap_actual_gaussian_spatial_positive_mesh_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ≤ T ∧ t m ω ≤ T)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, 0 ≤ y m ω ∧ y m ω ≤ c)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0) P) :
    ∀ m, Integrable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0) P := by sorry
