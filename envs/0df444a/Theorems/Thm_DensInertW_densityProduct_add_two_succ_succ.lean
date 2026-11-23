-- Prove2me | Theorems.Thm_DensInertW_densityProduct_add_two_succ_succ
-- name    : DensInertW.densityProduct_add_two_succ_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:39:04.765916+00:00
-- url     : https://prove2.me/theorems/19c7b0e4-9980-44aa-9afc-db04c1756645
-- title:
--   Dens Inert W: density Product add two succ succ
-- statement:
--   The Dens Inert W construction uses the density Product add two succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensityProductAddTwoSuccSucc.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensityProductAddTwoSuccSucc.lean#L58-L64

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

theorem DensInertW.densityProduct_add_two_succ_succ (q N c : ℕ) :
    Formalism.L2.SG.DensExact.densProd q (-1) (N + 2) (c + 1) (c + 1) =
      arF q (N + 2) * arF q (N + 1) * Formalism.L2.SG.DensExact.densProd q (-1) N c c := by sorry
