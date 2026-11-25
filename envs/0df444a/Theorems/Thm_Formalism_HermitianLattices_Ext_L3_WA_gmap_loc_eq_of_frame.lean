-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_gmap_loc_eq_of_frame
-- name    : Formalism.HermitianLattices.Ext.L3.WA.gmap_loc_eq_of_frame
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:13.565679+00:00
-- url     : https://prove2.me/theorems/3aade15a-09fe-418b-bd3e-2c754965e2c0
-- title:
--   WA: gmap loc eq of frame
-- statement:
--   The WA construction uses the gmap loc eq of frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/GmapLocEqOfFrame.lean#L54-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/GmapLocEqOfFrame.lean#L54-L108

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

theorem Formalism.HermitianLattices.Ext.L3.WA.gmap_loc_eq_of_frame {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {p : Ideal (𝓞 K)} (hp : p.IsPrime) (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) {n : ℕ} {e : Fin n → V}
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hge : ∀ i, g (e i) ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p (Submodule.span (𝓞 K) (Set.range e))) =
      Formalism.HermitianLatticesTheory.loc (K := K) p L := by sorry
