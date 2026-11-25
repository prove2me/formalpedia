-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_mem_box_sub
-- name    : CompanionTheory.LimBd.Main.mem_box_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:29.476914+00:00
-- url     : https://prove2.me/theorems/d36221af-8d4c-5f2f-a40f-53784a11de0d
-- title:
--   Main: mem box sub
-- statement:
--   The Main construction uses the mem box sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/Letter.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/Letter.lean#L73-L76

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

theorem CompanionTheory.LimBd.Main.mem_box_sub {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) : μ - Pi.single s 1 ∈ Box μ 1 := by sorry
