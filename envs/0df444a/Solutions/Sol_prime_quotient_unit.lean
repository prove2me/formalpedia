-- Prove2me | solution 1 for prime_quotient_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:08:20.6169+00:00
-- url     : https://prove2.me/submissions/2f9791ed-a6f4-47d6-9fe9-58548bd7af7b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PinHostLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalResidueCharacter_ResCharEq
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PinHostLoc
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_irr
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_resChar_eq
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_unit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false

theorem _root_.solution : PI.PinHostLoc.Target := by
  intro F E _ _ _ _ _ sig p A g hg hne i hin hnot
  have hres := PI.PinHostLoc.UnitaryGroupMassFormula.resChar_eq p (hg i) hin
  have hi0 : ((g i : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (hg i).ne_zero
  refine ⟨?_, ?_⟩
  · rw [hres]
    exact PI.PinHostLoc.UnitaryGroupMassFormula.irr A (hg i).ne_zero hin hnot
  · obtain ⟨j, hgij, hj⟩ : ∃ j : Fin 2, g i ≠ g j ∧
        ((g 0 : ℕ) : F) * ((g 1 : ℕ) : F) / ((g i : ℕ) : F) = ((g j : ℕ) : F) := by
      rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
      · exact ⟨1, hne, mul_div_cancel_left₀ _ hi0⟩
      · exact ⟨0, hne.symm, mul_div_cancel_right₀ _ hi0⟩
    have hjp : ((g j : ℕ) : NumberField.RingOfIntegers F) ∉ p.asIdeal := by
      intro hjin
      have hcop : IsCoprime ((g i : ℕ) : ℤ) ((g j : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hg i) (hg j)).mpr hgij)
      obtain ⟨a, b, hab⟩ := hcop
      have h1 : (1 : NumberField.RingOfIntegers F) ∈ p.asIdeal := by
        have h2 := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers F) hab
        push_cast at h2
        rw [← h2]
        exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hin) (p.asIdeal.mul_mem_left _ hjin)
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨u, hu, hu'⟩ := PI.PinHostLoc.UnitaryGroupMassFormula.unit A hjp
    exact ⟨u, hu, by rw [hu', hj]⟩
