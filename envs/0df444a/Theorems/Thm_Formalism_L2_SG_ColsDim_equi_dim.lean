-- Prove2me | Theorems.Thm_Formalism_L2_SG_ColsDim_equi_dim
-- name    : Formalism.L2.SG.ColsDim.equi_dim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:02.238027+00:00
-- url     : https://prove2.me/theorems/8ecda0e6-69fe-490c-9e98-b990f637500a
-- title:
--   Cols Dim: equi dim
-- statement:
--   The Cols Dim construction uses the equi dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L238-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L238-L248

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
variable {k : Type} [Field k] {W : Type} [AddCommGroup W] [Module k W]

theorem Formalism.L2.SG.ColsDim.equi_dim (hst : StabTriv ιf K) [Finite (Classes ιf K)] [FiniteDimensional k W]
    (ρ : Representation k Γ W) (χ : K →* kˣ) :
    FiniteDimensional k (Equi k ιf K ρ χ) ∧
      finrank k (Equi k ιf K ρ χ) = finrank k W * Nat.card (Classes ιf K) := by sorry
