-- Prove2me | Theorems.Thm_CMDeg_sigma_ne_one
-- name    : CMDeg.sigma_ne_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:20.673833+00:00
-- url     : https://prove2.me/theorems/60526241-941a-49bd-8fb1-8c02448a0254
-- title:
--   CMDeg: sigma ne one
-- statement:
--   The CMDeg construction uses the sigma ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDegreeEquality/FinrankEqTwo.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDegreeEquality/FinrankEqTwo.lean#L34-L40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open CMDeg
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem CMDeg.sigma_ne_one (hE : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) : sigma hfix ≠ 1 := by sorry
