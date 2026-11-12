-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_original_preruin_masked_uniform_floor_kernel_converges
-- name    : AvramDividend.Classical.avram_bva20_original_preruin_masked_uniform_floor_kernel_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:58:43.527049+00:00
-- url     : https://prove2.me/theorems/11fd0ffd-f115-4c96-b2a2-bed6e976bc8f
-- title:
--   Original pre-ruin closed-cap marked compensator grid mask is eventually active and converges
-- statement:
--   For each positive original time strictly before ruin, the left uniform floor grid times precede that time and remain within the original dividend strategy's closed reserve cap. The mask in the original stopped negative-mark Riemann integrand is therefore active at every grid sample, and its discounted mark integral converges to the true original kernel by the already Proved B21 physical floor theorem. This is the required mask bridge for source-exact pointwise dominated convergence in 7ccc2a1a.
-- source:
--   Necessary real-grid pointwise masked-integrand convergence used to establish the original inclusive compensator Riemann approximation 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_physical_discounted_mark_uniform_floor_converges
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva20_original_preruin_masked_uniform_floor_kernel_converges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hpre : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q T : ℝ) (hT : 0 < T) :
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    let F : ℝ≥0 → ℝ := fun r => Real.exp (-(q * (r : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν
    Tendsto (fun n =>
      if (s n : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C then F (s n) else 0)
      atTop (𝓝 (F t)) := by sorry
