-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_kfin_iff
-- name    : CompanionTheory.LimBd.Main.kfin_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:29:46.078006+00:00
-- url     : https://prove2.me/theorems/6eb6358e-03c2-50e9-b724-807aefc4b624
-- title:
--   Main: kfin iff
-- statement:
--   The Main construction uses the kfin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/Letter.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/Letter.lean#L39-L48

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

theorem CompanionTheory.LimBd.Main.kfin_iff {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (hP : IsCayleyU k r ε P)
    (σ : B.Mat k r → (H →L[ℂ] H)) (v : H) :
    IsKFinHpk (k := k) (r := r) σ v ↔ IsKFin ε (fun g => σ (P⁻¹ * g * P)) v := by sorry
