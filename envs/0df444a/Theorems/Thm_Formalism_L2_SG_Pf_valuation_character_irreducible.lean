-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_valuation_character_irreducible
-- name    : Formalism.L2.SG.Pf.valuation_character_irreducible
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:55:07.260328+00:00
-- url     : https://prove2.me/theorems/c046cec2-d095-5753-9d2c-d5b75bc7b2f9
-- title:
--   Pf: valuation character irreducible
-- statement:
--   The Pf construction uses the valuation character irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ColDictValCPf.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ColDictValCPf.lean#L12-L15

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ColDictValC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_IsUnitDetOfUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivisorClosedHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_CayleyIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ColDictValCPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf

theorem Formalism.L2.SG.Pf.valuation_character_irreducible : ColDictPf.ValCIrr := by sorry
