-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_marked_negative_jump_kernel_eventually_unmasked_on_any_fixed_compact
-- name    : AvramDividend.Classical.avram_bva_a22_original_marked_negative_jump_kernel_eventually_unmasked_on_any_fixed_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:29:47.459867+00:00
-- url     : https://prove2.me/theorems/2b3d8e28-d945-431b-ac32-1492923983c7
-- title:
--   Original negative-mark compensated jump integrand becomes exactly unmasked on every fixed interior compact for all sufficiently large arbitrary spatial band rows
-- statement:
--   For the authentic original filtered spectrally negative Levy source and admissible original dividend control, consider its exact stopped pre-right-payment left-limit reserve and original negative jump mark z<0. Given arbitrary prescribed cofinal interior band sequences a(n),b(n), and any fixed compact [c,d] strictly inside (0,C), prove that beyond one deterministic band threshold, the original time-stopped, spatially masked, discounted negative-mark integrand is literally equal to the unmasked original discounted jump candidate increment at all clocks t before min(ruin,S), all paths and all negative marks whose reserve lies in that fixed compact. Reuse the Proved original BVA-A22 stopped compact coverage theorem. This is a source-exact localisation identity for the BVA96 arbitrary-band compensated jump convergence; it assumes no rate between spatial and physical grid rows, finite activity or generator L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_ruinstopped_prepayment_compact_allband
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_marked_negative_jump_kernel_eventually_unmasked_on_any_fixed_compact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hcC : ENNReal.ofReal c < C) (hdC : ENNReal.ofReal d < C) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      Function.leftLim (fun r : ℝ≥0 =>
        x + X.X r ω - rightLimit D r ω) t
    ∃ N : ℕ, ∀ n ≥ N, ∀ (S : ℝ≥0) (ω : Ω) (t : ℝ≥0) (z : ℝ),
      (t : ℝ≥0∞) ≤ min (ruinTime X x D ω) (S : ℝ≥0∞) →
      Y t ω ∈ Icc c d → z < 0 →
      (if (((t : ℝ≥0∞) ≤
          min (ruinTime X x D ω) (S : ℝ≥0∞) ∧
          Y t ω ∈ Icc (a n) (b n)) ∧ z < 0) then
        Real.exp (-(q * (t : ℝ))) * (w (Y t ω + z) - w (Y t ω))
      else 0) =
        Real.exp (-(q * (t : ℝ))) * (w (Y t ω + z) - w (Y t ω)) := by sorry
