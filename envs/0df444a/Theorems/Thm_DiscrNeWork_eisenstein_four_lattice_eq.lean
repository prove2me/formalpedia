-- Prove2me | Theorems.Thm_DiscrNeWork_eisenstein_four_lattice_eq
-- name    : DiscrNeWork.eisenstein_four_lattice_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:38.735095+00:00
-- url     : https://prove2.me/theorems/a316621b-05dd-45ff-b659-2eddc54170c9
-- title:
--   Discr Ne Work: eisenstein four lattice eq
-- statement:
--   The Discr Ne Work construction uses the eisenstein four lattice eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscMain.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscMain.lean#L91-L98

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscMain
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

theorem DiscrNeWork.eisenstein_four_lattice_eq (a : ℂ) (ha : a ≠ 0) (τ : ℍ) :
    PI.eisG (PI.lat2 a (a * τ)) 2 = (a ^ 4)⁻¹ * ((Real.pi : ℂ) ^ 4 / 90 * (2 * E₄ τ)) := by sorry
