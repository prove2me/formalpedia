-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_split_prime_local_holds
-- name    : Formalism.L2.SG.Pf.SatGramLoc.split_prime_local_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:14.314092+00:00
-- url     : https://prove2.me/theorems/7e01c231-3c3f-4694-a6e3-bea1932def56
-- title:
--   Sat Gram Loc: split prime local holds
-- statement:
--   The Sat Gram Loc construction uses the split prime local holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfA.lean#L158-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfA.lean#L158-L174

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfA
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

theorem Formalism.L2.SG.Pf.SatGramLoc.split_prime_local_holds : SplitPrimeLoc := by sorry
