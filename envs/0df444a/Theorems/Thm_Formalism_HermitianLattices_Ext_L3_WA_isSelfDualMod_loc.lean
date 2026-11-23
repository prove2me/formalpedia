-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_isSelfDualMod_loc
-- name    : Formalism.HermitianLattices.Ext.L3.WA.isSelfDualMod_loc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:39.610514+00:00
-- url     : https://prove2.me/theorems/41a0dee6-81c7-4c48-98c2-2806c94b18f8
-- title:
--   WA: is Self Dual Mod loc
-- statement:
--   The WA construction uses the is Self Dual Mod loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/GmapLocEqOfFrame.lean#L31-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/GmapLocEqOfFrame.lean#L31-L52

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsHermSemilocalLocRing
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.WA.isSelfDualMod_loc {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) {p : Ideal (𝓞 K)} (hp : p.IsPrime)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    IsSelfDualMod (locRing p) h (Formalism.HermitianLatticesTheory.loc (K := K) p L).toAddSubgroup := by sorry
