-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_gmap_injective
-- name    : Formalism.HermitianLattices.Ext.L3.gmap_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:29.91848+00:00
-- url     : https://prove2.me/theorems/6f588dba-af2f-4542-bb31-a82d53461ffe
-- title:
--   L3: gmap injective
-- statement:
--   The L3 construction uses the gmap injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/UnimodularOfMemGenusOrtho.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/UnimodularOfMemGenusOrtho.lean#L29-L34

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnimodularOfMemGenusOrtho
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.gmap_injective (g : V ≃ₗ[K] V) :
    Function.Injective (Formalism.HermitianLatticesTheory.gmap g : Submodule (𝓞 K) V → Submodule (𝓞 K) V) := by sorry
