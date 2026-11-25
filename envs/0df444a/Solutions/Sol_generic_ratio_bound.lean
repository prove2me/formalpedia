-- Prove2me | solution 1 for generic_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:08:04.443214+00:00
-- url     : https://prove2.me/submissions/2d437f3d-98a2-46a0-8527-8a98a0c3e7b2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GenericRatioBound_GenericRatioOfBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GGGenRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.L2.SG.GGMirabolic.GenericRatioOfBound := by
  unfold Formalism.L2.SG.GGMirabolic.GenericRatioOfBound
  intro hMir hCard
  unfold Formalism.L2.SG.GGMirabolic.GenericRatio
  intro F _ _ k ψ₀ hψ V _ _ _ π hirr hgen
  have hb := hMir F k ψ₀ hψ V π hirr hgen
  rw [hCard F k]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqR : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hx : ∀ i ∈ Finset.Ico 1 k, (1 : ℝ) < (Fintype.card F : ℝ) ^ i := by
    intro i hi
    have hi1 : i ≠ 0 := by
      simp only [Finset.mem_Ico] at hi
      omega
    exact one_lt_pow₀ hqR hi1
  have hsum : ∑ i ∈ Finset.Ico 1 k, i = k * (k - 1) / 2 := by
    rw [← Finset.sum_range_id]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
      simp
  have hP : 0 < ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) :=
    Finset.prod_pos fun i hi => sub_pos.mpr (hx i hi)
  have hcast : ((∏ i ∈ Finset.Ico 1 k, (Fintype.card F ^ i - 1) : ℕ) : ℝ)
      = ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hPD : ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) ≤ (Module.finrank ℂ V : ℝ) := by
    rw [← hcast]
    exact_mod_cast hb
  have hR : ∏ i ∈ Finset.Ico 1 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)⁻¹
      = (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have h1 := hx i hi
    have h0 : (Fintype.card F : ℝ) ^ i ≠ 0 := (lt_trans one_pos h1).ne'
    have h2 : (Fintype.card F : ℝ) ^ i - 1 ≠ 0 := (sub_pos.mpr h1).ne'
    field_simp
  rw [hR, Nat.cast_pow]
  gcongr
  all_goals first
    | exact hPD
    | exact hP.le
    | exact hP
    | positivity
