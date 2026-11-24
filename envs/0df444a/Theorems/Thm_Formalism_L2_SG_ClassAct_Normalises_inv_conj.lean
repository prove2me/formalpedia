-- Prove2me | Theorems.Thm_Formalism_L2_SG_ClassAct_Normalises_inv_conj
-- name    : Formalism.L2.SG.ClassAct.Normalises.inv_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:48.249842+00:00
-- url     : https://prove2.me/theorems/7c54401f-1147-4afb-91db-95d19d9c77d1
-- title:
--   Normalises: inv conj
-- statement:
--   The Normalises construction uses the inv conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ClassAct.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ClassAct.lean#L16-L19

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

theorem Formalism.L2.SG.ClassAct.Normalises.inv_conj {D K : Subgroup G} (h : Normalises D K) {δ : G} (hδ : δ ∈ D) {κ : G}
    (hκ : κ ∈ K) : δ⁻¹ * κ * δ ∈ K := by sorry
