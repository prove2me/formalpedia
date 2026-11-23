-- Prove2me | Theorems.Thm_DensInertW_ar_zero_prod
-- name    : DensInertW.ar_zero_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:26.230862+00:00
-- url     : https://prove2.me/theorems/7ff92213-8cd0-4c48-8732-47aa0bd0eeba
-- title:
--   Dens Inert W: ar zero prod
-- statement:
--   The Dens Inert W construction uses the ar zero prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensityProductAddTwoSuccSucc.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensityProductAddTwoSuccSucc.lean#L66-L69

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensExactInertOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensityProductAddTwoSuccSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open DensInertW

theorem DensInertW.ar_zero_prod (q n m c : ℕ) (h : n + 1 ≤ m + c) :
    Formalism.L2.SG.DensExact.densProd q (-1) n m c = 0 := by sorry
