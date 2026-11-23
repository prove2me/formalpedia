-- Prove2me | solution 1 for instUniqueFactorizationMonoidPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:23:51.132975+00:00
-- url     : https://prove2.me/submissions/f6703f14-0def-4a1e-bf1f-77d8e6bc2dec

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
import Definitions.Def_Kaplanski4_Kaplanski
import Theorems.Thm_uniqueFactorizationMonoid_iff

set_option autoImplicit false
variable {R : Type*}
variable [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
open PowerSeries Set Ideal
theorem _root_.solution : UniqueFactorizationMonoid R⟦X⟧ := by
  refine uniqueFactorizationMonoid_iff.mpr (fun P h₁ h₂ ↦ ?_)
  by_cases hXP : X ∈ P
  · exact ⟨X, hXP, X_prime⟩
  · obtain ⟨_, h⟩ := (IsPrincipalIdealRing.principal (P.map constantCoeff)).principal
    obtain ⟨_, rfl, _, h⟩ := exist_eq_span_eq_ncard_of_X_notMem hXP h.symm (finite_singleton _)
    simp only [ncard_singleton, ncard_eq_one] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨_, mem_span_singleton_self _,
      (span_singleton_prime (span_singleton_eq_bot.not.1 h₁)).1 h₂⟩
