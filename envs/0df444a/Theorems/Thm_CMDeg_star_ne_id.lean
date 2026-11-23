-- Prove2me | Theorems.Thm_CMDeg_star_ne_id
-- name    : CMDeg.star_ne_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:21.944691+00:00
-- url     : https://prove2.me/theorems/bed55ad0-42f5-4a2f-bb7a-08da9fc49480
-- title:
--   CMDeg: star ne id
-- statement:
--   The CMDeg construction uses the star ne id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDegreeEquality/FinrankEqTwo.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDegreeEquality/FinrankEqTwo.lean#L23-L32

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

theorem CMDeg.star_ne_id (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) : ∃ a : E, star a ≠ a := by sorry
