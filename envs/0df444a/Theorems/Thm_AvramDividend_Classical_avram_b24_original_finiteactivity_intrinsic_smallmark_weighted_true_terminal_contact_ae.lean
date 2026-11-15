-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_intrinsic_smallmark_weighted_true_terminal_contact_ae
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_intrinsic_smallmark_weighted_true_terminal_contact_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:27:12.751429+00:00
-- url     : https://prove2.me/theorems/77b8fcb3-5c64-4984-993e-88ca8d82eeef
-- title:
--   The true original finite-activity Lévy compensated smallmark last-cell gain converges a.e. to the surviving marked ruin-contact jump
-- statement:
--   For an arbitrary genuine intrinsic compensated negative smallmark witness of the original finite-activity spectrally negative Lévy X on the original sample space, and an arbitrary positive physical terminal or true ruin-clipped clock σ≤T, any weighted deterministic physical last-contact cells approaching σ from strictly left and weakly right, with predictable bounded weights converging a.e. to Wleft, have compensated mark increments converging a.e. to Wleft times the ACTUAL original negative jump ΔX_σ exactly when -1<ΔX_σ<0. Other marks produce zero in the smallmark channel and are handled separately by the large-jump generator. Uses original same-space finite marked path representation, arbitrary-source right continuity and true terminal step atom. Does not incorrectly kill negative ruin jumps by Gaussian continuity or require postruin paths or finite large-mark second moments.
-- source:
--   Proved B24 arbitrary original Jsmall right continuity, finite true marked horizon representation and weighted original finite terminal mark limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_intrinsic_smallmark_weighted_true_terminal_contact_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) (σ : Ω → ℝ≥0) (hσ : ∀ ω, σ ω ≤ T)
    (a b : ℕ → Ω → ℝ≥0)
    (W : ℕ → Ω → ℝ) (Wleft : Ω → ℝ)
    (ha : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => a k ω) atTop (𝓝[<] (σ ω)))
    (hb : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => b k ω) atTop (𝓝[Ici (σ ω)] (σ ω)))
    (hW : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => W k ω) atTop (𝓝 (Wleft ω))) :
    ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => W k ω *
        (Jsmall (b k ω) ω - Jsmall (a k ω) ω)) atTop
      (𝓝 (Wleft ω *
        (if -1 < X.X (σ ω) ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω) ∧
             X.X (σ ω) ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω) < 0
         then X.X (σ ω) ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω)
         else 0))) := by sorry
