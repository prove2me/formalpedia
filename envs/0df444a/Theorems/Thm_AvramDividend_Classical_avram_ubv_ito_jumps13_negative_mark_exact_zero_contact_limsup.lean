-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps13_negative_mark_exact_zero_contact_limsup
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps13_negative_mark_exact_zero_contact_limsup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T15:37:43.328633+00:00
-- url     : https://prove2.me/theorems/3766ced6-ada8-42be-b971-bde9e2998cd9
-- title:
--   Negative Lévy jump exactly reaching reserve zero has correct upper semicontinuous mesh limit
-- statement:
--   At a negative Lévy mark z satisfying y+z=0, any original-trajectory pre-jump approximation approaching y has candidate value eventually below w(0)+ε. This justifies an upper residual estimate even when w(0)>0 and w is zero below reserve zero; exact-contact atoms must be retained, never discarded by a false continuity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-! An atom of the negative Levy measure may land exactly at reserve zero. -/

theorem AvramDividend.Classical.avram_ubv_ito_jumps13_negative_mark_exact_zero_contact_limsup
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ v : ℝ, v < 0 → w v = 0)
    (y z : ℝ) (hy : 0 < y) (hz : z < 0) (hcontact : y + z = 0)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, w (u n + z) ≤ w 0 + ε := by sorry
