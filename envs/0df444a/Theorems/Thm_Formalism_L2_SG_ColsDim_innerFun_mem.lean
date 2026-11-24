-- Prove2me | Theorems.Thm_Formalism_L2_SG_ColsDim_innerFun_mem
-- name    : Formalism.L2.SG.ColsDim.innerFun_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:15.643858+00:00
-- url     : https://prove2.me/theorems/a321f982-a37e-40a6-92bc-3c532761c1d6
-- title:
--   Cols Dim: inner Fun mem
-- statement:
--   The Cols Dim construction uses the inner Fun mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L362-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ColsDim.lean#L362-L372

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

theorem Formalism.L2.SG.ColsDim.innerFun_mem (ιi : Γ →* Gi) (ψ : K →* ℂˣ) (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, inner ℂ (π h v) (π h w) = inner ℂ v w)
    (hψ : ∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) (φ : Sharp ℂ ιi ιf K π ψ) :
    (fun x => (innerₛₗ ℂ ((φ : Gf → V) x) : Dual ℂ V)) ∈ Equi ℂ ιf K (dualRep ιi π) ψ := by sorry
