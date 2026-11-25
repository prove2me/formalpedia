-- Prove2me | Theorems.Thm_DiscrNeWork_eisG_eq
-- name    : DiscrNeWork.eisG_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:17:50.455578+00:00
-- url     : https://prove2.me/theorems/bcc6f6b9-8bf9-5d87-bb70-daf45cb18d3e
-- title:
--   Discr Ne Work: eis G eq
-- statement:
--   The Discr Ne Work construction uses the eis G eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscLat.lean#L81-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscLat.lean#L81-L122

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ModularForm EisensteinSeries UpperHalfPlane
noncomputable section
open DiscrNeWork

theorem DiscrNeWork.eisG_eq (a : ℂ) (ha : a ≠ 0) (τ : ℍ) (k : ℕ) (hk : 1 ≤ k) :
    PI.eisG (PI.lat2 a (a * τ)) k =
      (a ^ (2 * k))⁻¹ * ∑' v : Fin 2 → ℤ, eisSummand ((2 * k : ℕ) : ℤ) v τ := by sorry
