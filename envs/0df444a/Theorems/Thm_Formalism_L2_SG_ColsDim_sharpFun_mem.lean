-- Prove2me | Theorems.Thm_Formalism_L2_SG_ColsDim_sharpFun_mem
-- name    : Formalism.L2.SG.ColsDim.sharpFun_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:27.436863+00:00
-- url     : https://prove2.me/theorems/89212376-5383-4eca-b3cf-5ba3158f018a
-- title:
--   Cols Dim: sharp Fun mem
-- statement:
--   The Cols Dim construction uses the sharp Fun mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L348-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L348-L360

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

theorem Formalism.L2.SG.ColsDim.sharpFun_mem (ιi : Γ →* Gi) (ψ : K →* ℂˣ) (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, inner ℂ (π h v) (π h w) = inner ℂ v w)
    (hψ : ∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) (f : Equi ℂ ιf K (dualRep ιi π) ψ) :
    sharpFun (f : Gf → Dual ℂ V) ∈ Sharp ℂ ιi ιf K π ψ := by sorry
