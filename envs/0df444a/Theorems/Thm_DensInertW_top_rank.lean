-- Prove2me | Theorems.Thm_DensInertW_top_rank
-- name    : DensInertW.top_rank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:36.628214+00:00
-- url     : https://prove2.me/theorems/7ddd08c5-604c-49a1-a9f4-84f74c630c21
-- title:
--   Dens Inert W: top rank
-- statement:
--   The Dens Inert W construction uses the top rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensExactInertOf.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensExactInertOf.lean#L94-L104

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensExactInertOf
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

theorem DensInertW.top_rank (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (m : ℕ) (B P : Matrix (Fin m) (Fin m) L) (hP : IsUnit P.det) :
    (P * B * (P.map (fun y => y ^ Fintype.card K)).transpose).rank = B.rank := by sorry
