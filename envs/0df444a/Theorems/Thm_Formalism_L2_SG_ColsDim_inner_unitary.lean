-- Prove2me | Theorems.Thm_Formalism_L2_SG_ColsDim_inner_unitary
-- name    : Formalism.L2.SG.ColsDim.inner_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:42.799077+00:00
-- url     : https://prove2.me/theorems/5e946bc9-97e9-44fa-a739-f6466f9668e8
-- title:
--   Cols Dim: inner unitary
-- statement:
--   The Cols Dim construction uses the inner unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L333-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L333-L337

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
open InnerProductSpace
variable {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem Formalism.L2.SG.ColsDim.inner_unitary (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, inner ℂ (π h v) (π h w) = inner ℂ v w) (h : Gi) (v w : V) :
    inner ℂ (π h v) w = inner ℂ v (π h⁻¹ w) := by sorry
