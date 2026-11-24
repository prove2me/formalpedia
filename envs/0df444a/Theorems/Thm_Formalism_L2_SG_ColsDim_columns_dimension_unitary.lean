-- Prove2me | Theorems.Thm_Formalism_L2_SG_ColsDim_columns_dimension_unitary
-- name    : Formalism.L2.SG.ColsDim.columns_dimension_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:24.446905+00:00
-- url     : https://prove2.me/theorems/c3327f96-9590-48ed-adb9-c7913f0ce06d
-- title:
--   Cols Dim: columns dimension unitary
-- statement:
--   The Cols Dim construction uses the columns dimension unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L422-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L422-L424

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.ColsDim
open Formalism.UG

theorem Formalism.L2.SG.ColsDim.columns_dimension_unitary : ColsDimU := by sorry
