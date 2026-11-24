-- Prove2me | Theorems.Thm_Formalism_L2_SG_ClassAct_diaFree_of_isNeat
-- name    : Formalism.L2.SG.ClassAct.diaFree_of_isNeat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:46.077504+00:00
-- url     : https://prove2.me/theorems/cc7bf0c7-8e30-4edc-95ba-0a0ee0f57767
-- title:
--   Class Act: dia Free of is Neat
-- statement:
--   The Class Act construction uses the dia Free of is Neat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ClassAct.lean#L31-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ClassAct.lean#L31-L56

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.ClassAct
open Formalism.UG Module
variable {G : Type} [Group G]

theorem Formalism.L2.SG.ClassAct.diaFree_of_isNeat {Γ K K₀ D : Subgroup G} (hK : K ≤ K₀) (hD : D ≤ K₀) (hn : IsNeat Γ K₀) :
    DiaFree Γ K D := by sorry
