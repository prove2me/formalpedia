-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_dot_transport
-- name    : CompanionTheory.LimBd.Main.dot_transport
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:57:15.022957+00:00
-- url     : https://prove2.me/theorems/73cdac27-8929-42df-969d-00bcf37a808d
-- title:
--   Main: dot transport
-- statement:
--   The Main construction uses the dot transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/Letter.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/Letter.lean#L85-L90

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : B.Mat k r}

theorem CompanionTheory.LimBd.Main.dot_transport (hP : IsCayleyU k r ε P) (a : B.Mat k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    star (P *ᵥ y) ⬝ᵥ ((P * a * P⁻¹) *ᵥ (P *ᵥ x)) = star y ⬝ᵥ (a *ᵥ x) := by sorry
