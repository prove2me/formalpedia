-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_capped_stopped_reserve_generator_certificate
-- name    : AvramDividend.Classical.avram_bv_gen8_original_capped_stopped_reserve_generator_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:52:09.387143+00:00
-- url     : https://prove2.me/theorems/a15ec73e-8a01-4911-a273-5b8853b71f71
-- title:
--   Original cstar-capped stopped reserve is generator-integrable and q-harmonic at every active positive time
-- statement:
--   For the actual spectrally negative BV Levy process and original cstar-capped admissible dividend strategy, at every stopped physical time including zero with positive post-right-payment reserve, vcstar is generator-integrable and its generator minus q times value equals zero. Combines proved original reserve cap a009975c with proved closed-cap BV generator certificate 0de73404.
-- source:
--   Direct original-process bridge from a009975c to 0de73404; no mesh, generator assumption above cstar, abstract-process replacement or nonlocal envelope.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_original_capped_stopped_reserve_generator_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ cstar W)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (cstar W) D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      let Z : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      0 < Z →
        X.GeneratorIntegrable (vcstar W) Z ∧
          X.generator (vcstar W) Z - q * vcstar W Z = 0 := by sorry
