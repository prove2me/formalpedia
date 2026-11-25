-- Prove2me | Theorems.Thm_DensInertW_ar_densProd_eq
-- name    : DensInertW.ar_densProd_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:17:46.955886+00:00
-- url     : https://prove2.me/theorems/7de4b3f0-7e74-4aad-9e8a-a26efb80eadb
-- title:
--   Dens Inert W: ar dens Prod eq
-- statement:
--   The Dens Inert W construction uses the ar dens Prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensityProductAddTwoSuccSucc.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensityProductAddTwoSuccSucc.lean#L14-L15

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

theorem DensInertW.ar_densProd_eq (q n m c : ℕ) :
    Formalism.L2.SG.DensExact.densProd q (-1) n m c = ∏ i ∈ Icc (n + 1 - (m + c)) n, arF q i := by sorry
