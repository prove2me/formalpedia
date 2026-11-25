-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_cut_gmap_extOf
-- name    : Formalism.HermitianLattices.Ext.L3.StabilizerLattices.cut_gmap_extOf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:00:55.98926+00:00
-- url     : https://prove2.me/theorems/7568f9b6-61a0-4d38-8bf3-9879c3b374a2
-- title:
--   Stabilizer Lattices: cut gmap ext Of
-- statement:
--   The Stabilizer Lattices construction uses the cut gmap ext Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSmulMem.lean#L156-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSmulMem.lean#L156-L160

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Definitions.Def_Lemmata_GeneralBFactSecondForm_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
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
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open SplitBAux

theorem Formalism.HermitianLattices.Ext.L3.StabilizerLattices.cut_gmap_extOf (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (Λ : Submodule (𝓞 K) V) :
    S.cut (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = Formalism.HermitianLatticesTheory.gmap g' (S.cut Λ) := by sorry
