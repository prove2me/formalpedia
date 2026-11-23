-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_smul_mem_loc
-- name    : Formalism.HermitianLattices.Ext.L3.WA.smul_mem_loc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:48.616694+00:00
-- url     : https://prove2.me/theorems/275616ce-dd5f-4d5c-9003-a2358dabdbf0
-- title:
--   WA: smul mem loc
-- statement:
--   The WA construction uses the smul mem loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/GmapLocEqOfFrame.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/GmapLocEqOfFrame.lean#L16-L29

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

theorem Formalism.HermitianLattices.Ext.L3.WA.smul_mem_loc {L : Submodule (𝓞 K) V} {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K}
    (ha : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) {m : V} (hm : m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    a • m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by sorry
