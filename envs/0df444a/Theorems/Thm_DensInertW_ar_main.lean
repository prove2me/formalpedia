-- Prove2me | Theorems.Thm_DensInertW_ar_main
-- name    : DensInertW.ar_main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:52.0169+00:00
-- url     : https://prove2.me/theorems/3debd5f5-2c6d-4fc0-9d87-7a8f07def741
-- title:
--   Dens Inert W: ar main
-- statement:
--   The Dens Inert W construction uses the ar main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensityProductAddTwoSuccSucc.lean#L105-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensityProductAddTwoSuccSucc.lean#L105-L128

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

theorem DensInertW.ar_main (q : ℕ) (hq : 0 < q) : ∀ r c n : ℕ,
    ((Fr q n r c : ℤ) : ℝ) * (q : ℝ) ^ ((r + c) ^ 2) =
      (q : ℝ) ^ (2 * n * (r + c)) * Formalism.L2.SG.DensExact.densProd q (-1) n (r + c) c := by sorry
