-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_coe_map_injective
-- name    : Formalism.FG.HeightVAux.coe_map_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:21.260045+00:00
-- url     : https://prove2.me/theorems/36959082-30b9-4084-8904-9869824d38f9
-- title:
--   Height VAux: coe map injective
-- statement:
--   The Height VAux construction uses the coe map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L118-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L118-L125

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.HeightVAux
open MvPowerSeries Formalism.G Formalism.LT
variable {l : ℕ} [Fact l.Prime]

theorem Formalism.FG.HeightVAux.coe_map_injective {σ : Type*} :
    Function.Injective (map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) :
      MvPowerSeries σ ℤ_[l] → MvPowerSeries σ ℚ_[l]) := by sorry
