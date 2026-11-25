-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_isCoef_of_J
-- name    : CompanionTheory.LimBd.Main.isCoef_of_J
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:57:09.924441+00:00
-- url     : https://prove2.me/theorems/32c820eb-8462-444c-b9e4-2d46c24452ad
-- title:
--   Main: is Coef of J
-- statement:
--   The Main construction uses the is Coef of J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/Letter.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/Letter.lean#L55-L64

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

theorem CompanionTheory.LimBd.Main.isCoef_of_J (hP : IsCayleyU k r ε P) {μ : Fin (2 * r + k + 1) → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {τ : B.Mat k r → (H →L[ℂ] H)} (hμ : IsHCParam μ) (hτ : IsDS ε μ τ)
    {v w : H} (hv : IsKFin ε τ v) (hw : IsKFin ε τ w) :
    IsCoef k r ε μ fun x => ⟪w, τ (P * x * P⁻¹) v⟫_ℂ := by sorry
