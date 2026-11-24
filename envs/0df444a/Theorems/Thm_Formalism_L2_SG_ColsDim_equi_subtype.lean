-- Prove2me | Theorems.Thm_Formalism_L2_SG_ColsDim_equi_subtype
-- name    : Formalism.L2.SG.ColsDim.equi_subtype
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:04.927808+00:00
-- url     : https://prove2.me/theorems/6da26d65-dbd5-45e0-ae21-f70152f6d989
-- title:
--   Cols Dim: equi subtype
-- statement:
--   The Cols Dim construction uses the equi subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L154-L156

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

theorem Formalism.L2.SG.ColsDim.equi_subtype {k : Type} [Field k] {W : Type} [AddCommGroup W] [Module k W]
    (Γ' : Subgroup Gf) (ρ : Representation k Γ' W) (χ : K →* kˣ) :
    Equi k Γ'.subtype K ρ χ = Formalism.L2.SG.ClassAct.AMFChi k Γ' K ρ χ := by sorry
