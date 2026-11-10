-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_past_future_onecell_lintegral_exact
-- name    : AvramDividend.Classical.avram_mixed_source13_original_annulus_past_future_onecell_lintegral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:37:33.760692+00:00
-- url     : https://prove2.me/theorems/c058b9d2-4320-46a3-9760-3edb328238b5
-- title:
--   Exact original physical negative annulus chronological one-cell second-factorial rate
-- statement:
--   For the same original spectrally negative Levy process on its literal probability space and right-continuous filtration, the expected product of the original negative annulus physical count before s and the same annulus count on the following cell (s,t] equals the product of their true finite Levy compensator rates. This follows from the already-Proved nested cutoff pathwise count identity and the existing original full-cutoff past/future arbitrary-Borel-mark factor theorem. It is the missing one-cell rate input for physical factorial moment 6ea0212e, with no auxiliary marked process, surrogate independence, or strong Poisson hypothesis.
-- source:
--   Source bridge: Proved f0104cbc original cutoff annulus count splitting; Proved db4d85db exact full cutoff past versus arbitrary future Borel count; Proved 34dbea70 original separated negative Borel zero-origin rate; Proved 61ef9f16 original finite time partition; use original J from X.X exactly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mixed_source13_original_annulus_past_future_onecell_lintegral_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n m : ℕ) (hnm : n ≤ m) :
    let c : ℝ := -(1 / ((n : ℝ) + 1))
    let d : ℝ := -(1 / ((m : ℝ) + 1))
    let B : Set ℝ := Ioc c d
    let J : ℝ≥0 → ℝ≥0 → Set ℝ → Ω → ℝ≥0∞ := fun a b C ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ C)
    (∫⁻ ω, J 0 s B ω * J s t B ω ∂P) =
      ((s : ℝ≥0∞) * X.ν B) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
