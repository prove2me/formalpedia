-- Prove2me | Theorems.Thm_Formalism_L2_SG_ColsDim_stabTriv_mono
-- name    : Formalism.L2.SG.ColsDim.stabTriv_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:51.949713+00:00
-- url     : https://prove2.me/theorems/a96f3352-0cb0-4738-8248-eddf0811665e
-- title:
--   Cols Dim: stab Triv mono
-- statement:
--   The Cols Dim construction uses the stab Triv mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L152-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L152-L152

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
variable {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf)

theorem Formalism.L2.SG.ColsDim.stabTriv_mono {K K0 : Subgroup Gf} (h : K ≤ K0) (hs : StabTriv ιf K0) : StabTriv ιf K := by sorry
