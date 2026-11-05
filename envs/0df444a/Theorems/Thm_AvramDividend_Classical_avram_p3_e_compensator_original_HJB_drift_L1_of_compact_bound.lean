-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_HJB_drift_L1_of_compact_bound
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_HJB_drift_L1_of_compact_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:37:22.030202+00:00
-- url     : https://prove2.me/theorems/d99a96b4-eaec-4c74-80d2-3a9d816cac0a
-- title:
--   Original stopped BV HJB drift L1 from compact generator bound and measurable interior
-- statement:
--   Source-exact integrability of the discounted original-X left-limit HJB drift on the genuine finite horizon: on the predictable interior E the reserve is contained in compact Icc a b, a generator-level H is uniformly bounded there, and its localised discounted process is AE strongly measurable. The original probability measure and finite time product measure then give the actual drift L1 hypothesis for P3. H can be instantiated as X.drift*deriv w + integral_negative_jump - q*w.
-- source:
--   Proved public P3-E original finite-horizon product integrability lemma 00b5a3b3; literal source-X reserve prelimit and localised discounted HJB drift; Real.exp_le_exp and norm bounds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_horizon_drift_L1_of_uniform_bound
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_HJB_drift_L1_of_compact_bound
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
(q : ℝ) (hq : 0 ≤ q) (E : Set (ℝ≥0 × Ω))
(a b K : ℝ) (hK : 0 ≤ K) (H : ℝ → ℝ)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b)
(hHbound : ∀ y ∈ Set.Icc a b, |H y| ≤ K)
(hFm : AEStronglyMeasurable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by sorry
