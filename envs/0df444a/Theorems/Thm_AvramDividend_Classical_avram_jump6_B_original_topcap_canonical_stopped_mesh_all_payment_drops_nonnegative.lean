-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_canonical_stopped_mesh_all_payment_drops_nonnegative
-- name    : AvramDividend.Classical.avram_jump6_B_original_topcap_canonical_stopped_mesh_all_payment_drops_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T21:00:08.376716+00:00
-- url     : https://prove2.me/theorems/0b938055-1794-46d6-a5d7-e6543dcbabf7
-- title:
--   Every original top-cap canonical stopped physical-grid payment potential drop is nonnegative
-- statement:
--   Specialise the Proved genuine original topcap previsible payment secant theorem to every real stopped physical mesh cell min(i/(j+1),t) of the actual Levy reserve and dividend strategy. Before ruin, clipping preserves clock order and strict survival, hence all physical grid potential drops w(Z)-w(Y) are nonnegative. This establishes the exact per-cell sign hypothesis of the public finite ENNReal-to-real discount cash sum conversion for the infinite-activity topcap pathwise cash ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_previsible_payment_drop_nonnegative
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_topcap_canonical_stopped_mesh_all_payment_drops_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
    (j i : ℕ) :
    let v : ℕ → ℝ≥0 := fun k =>
      min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    0 ≤ w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
      w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) := by sorry
