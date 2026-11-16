-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_finite_jumps_eventually_affine_strict_left
-- name    : AvramDividend.Classical.avram_bva_finite_jumps_eventually_affine_strict_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:54:16.782082+00:00
-- url     : https://prove2.me/theorems/c14858f6-a2ff-4ccd-b5ff-dc4222a57d65
-- title:
--   Actual finite-jump drift path is eventually affine immediately before any jump
-- statement:
--   Given finitely many physical jumps and exact drift-only evolution whenever an interval contains no jumps, the original path agrees with an affine drift line on some strict-left neighbourhood of each jump time. The neighbourhood starts after the last preceding actual jump.
-- source:
--   Finite previous mark gap and physical no-jump interval drift evolution

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter Set AvramDividend.Classical
open scoped NNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_finite_jumps_eventually_affine_strict_left
    (f : ℝ≥0 → ℝ) (drift : ℝ) (T : ℝ≥0)
    (hFinite : Set.Finite {t : ℝ≥0 |
      0 < t ∧ t ≤ T ∧ f t - Function.leftLim f t ≠ 0})
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ Set.Ioc s t,
        f u - Function.leftLim f u = 0) →
      (t : ℝ) * drift - f t = (s : ℝ) * drift - f s)
    (u : ℝ≥0) (hu : u ∈ hFinite.toFinset) :
    ∃ a : ℝ, f =ᶠ[𝓝[<] u]
      (fun s : ℝ≥0 => a + drift * (s : ℝ)) := by sorry
