-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G4_nondegOn_cut
-- name    : Formalism.L2.SG.Pf.G4.nondegOn_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:26.390297+00:00
-- url     : https://prove2.me/theorems/b08ebeda-71e5-4034-ad35-d94e82d7f879
-- title:
--   G4: nondeg On cut
-- statement:
--   The G4 construction uses the nondeg On cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/AdelicThetaPoissonSummation.lean#L107-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/AdelicThetaPoissonSummation.lean#L107-L117

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G4
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}

theorem Formalism.L2.SG.Pf.G4.nondegOn_cut (hnd : NondegOn h W) {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    NondegOn h (cutW h W x) := by sorry
