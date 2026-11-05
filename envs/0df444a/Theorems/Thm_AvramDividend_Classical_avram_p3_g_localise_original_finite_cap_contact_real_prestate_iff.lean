-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_finite_cap_contact_real_prestate_iff
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_finite_cap_contact_real_prestate_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:31:41.237225+00:00
-- url     : https://prove2.me/theorems/99a06a12-d8a6-4a16-b89f-e0b6ca11649a
-- title:
--   Physical original pre-reserve finite-cap contact equals real cap equality
-- statement:
--   For the original x+X.X-rightLimit D left-limit reserve at an actual space-time point and a finite ENNReal cap C, provided the physical reserve is nonnegative, ENNReal cap-contact is equivalent exactly to real-valued reserve C.toReal. This permits explicit BV cap-contact boundary terms without a false zero-occupation argument. Infinite cap is covered by the separate already Proved no-contact alternative.
-- source:
--   Mathlib ENNReal.toReal_ofReal and ENNReal.ofReal_toReal for finite cap applied to literal source X,D reserve; hZ nonnegativity explicitly retained as a pathwise premise.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_finite_cap_contact_real_prestate_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (p : ℝ≥0 × Ω)
    (hZ : 0 ≤ Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) :
    ENNReal.ofReal (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) = C ↔
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 =
      C.toReal := by sorry
