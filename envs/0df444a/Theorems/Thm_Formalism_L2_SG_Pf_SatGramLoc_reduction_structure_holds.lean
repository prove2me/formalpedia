-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_reduction_structure_holds
-- name    : Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:29.824921+00:00
-- url     : https://prove2.me/theorems/177c6770-c5da-4cc1-89c9-46cfefc846cd
-- title:
--   Sat Gram Loc: reduction structure holds
-- statement:
--   The Sat Gram Loc construction uses the reduction structure holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfB.lean#L136-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfB.lean#L136-L225

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.SatGramLoc
attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds : RedCore := by sorry
