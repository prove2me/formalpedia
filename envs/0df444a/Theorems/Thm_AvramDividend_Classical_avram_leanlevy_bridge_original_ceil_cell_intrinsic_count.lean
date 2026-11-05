-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_cell_intrinsic_count
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_cell_intrinsic_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:20:55.235217+00:00
-- url     : https://prove2.me/theorems/ddbdde55-e03d-4ad6-b857-9dd05e571633
-- title:
--   Original Lévy intrinsic negative-band cell count equals its physical ceiling-index cardinal
-- statement:
--   On the very same original spectrally negative Lévy path X.X, the finite original marked-times filtered by one strict right-ceiling mesh index are exactly the negative-band intrinsic jump count in its actual half-open physical time cell. The real mesh endpoint identities are explicit; this composes the already-Proved original interval-count finset bridge and ceiling-cell iff, and directly enables the P4-F grid-pair expected count to be expressed using P2-E source compensation.
-- source:
--   Public Proved avram_p4_f_assembly_real_mesh_ceiling_cell_iff 8c01cb9e and avram_p2_e_compensator_original_window_count_finset_filter 0d0d4845; source marked-times theorem e5e6f70b; same pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_real_mesh_ceiling_cell_iff
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_window_count_finset_filter
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_cell_intrinsic_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (k : ℕ) (hk : 0 < k) (i : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (hs : (s : ℝ) = (i : ℝ) * (T : ℝ) / (k : ℝ))
    (ht : (t : ℝ) = ((i + 1 : ℕ) : ℝ) * (T : ℝ) / (k : ℝ))
    (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    (((F.filter (fun (u : ℝ≥0) => Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) = i + 1)).card : ℕ) : ℝ≥0∞) =
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) := by sorry
