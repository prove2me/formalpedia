-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_std_eq_zero
-- name    : CompanionTheory.D.gk.admitted.std_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:46.782402+00:00
-- url     : https://prove2.me/theorems/27a04099-77f8-4427-b5e6-0aaa73e8623e
-- title:
--   admitted: std eq zero
-- statement:
--   The admitted construction uses the std eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/SmallPI.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/SmallPI.lean#L7-L18

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_SmallPI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted

theorem CompanionTheory.D.gk.admitted.std_eq_zero {A : Type} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A] {M : ℕ} (hM : Module.finrank ℂ A < M)
    (b : Fin M → A) :
    ∑ π : Equiv.Perm (Fin M), ((Equiv.Perm.sign π : ℤ) : A) * (List.ofFn fun i => b (π i)).prod = 0 := by sorry
