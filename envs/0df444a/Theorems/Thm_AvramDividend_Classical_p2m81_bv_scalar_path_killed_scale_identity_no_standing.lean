-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_scalar_path_killed_scale_identity_no_standing
-- name    : AvramDividend.Classical.p2m81_bv_scalar_path_killed_scale_identity_no_standing
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T05:10:28.015809+00:00
-- url     : https://prove2.me/theorems/60a72977-db24-4719-8def-711fec1aaa40
-- title:
--   BV scalar whole-path killed scale identity from Esscher root without standing (public)
-- statement:
--   For a spectrally negative Levy process with positive discount q, positive Esscher root phi with psi(phi)=q, and genuine q-scale function W, the whole-path killed q-scale payoff at horizon T over paths surviving on the rational schedule is unbiased in the entire-path law: the path-measure lintegral of the schedule-killed discounted scale reward equals W(y) for every real reserve y. No Standing assumption; the root replaces Standing throughout.
-- source:
--   No-standing mirror of Proved avram_ws01b_bv_original_path_killed_scale_scalar (b1285a5a): fixed-time core via Proved avram_root29_01_deterministic_killed_qscale (094049ef), real/ennreal bridge via sibling H1a2 (inlined ofReal_integral_eq_lintegral_ofReal), schedule/measurability via standing-free Proved 67c7e86c/a484bed3/840bbf85. Supplies hScalar for the renewal kernel (8c2d238f) in parent H1 (ee75bf61).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.p2m81_bv_scalar_path_killed_scale_identity_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (T : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (y : ℝ) :
    (∫⁻ z : ℝ≥0 → ℝ,
      if ∀ j : ℕ, τ j ≤ T → 0 ≤ y + z (τ j) then
        ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (y + z T))
      else (0 : ℝ≥0∞)
      ∂(Measure.map (fun ω : Ω => (fun t : ℝ≥0 => X.X t ω)) P)) =
    ENNReal.ofReal (W y) := by sorry
