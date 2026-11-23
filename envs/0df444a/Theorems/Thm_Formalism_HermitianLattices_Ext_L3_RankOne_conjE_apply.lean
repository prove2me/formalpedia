-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_conjE_apply
-- name    : Formalism.HermitianLattices.Ext.L3.RankOne.conjE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:44.494801+00:00
-- url     : https://prove2.me/theorems/c1a728a6-1b79-4ab5-b98b-7b1d3ee6ac56
-- title:
--   Rank One: conj E apply
-- statement:
--   The Rank One construction uses the conj E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsClassRepsMap.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsClassRepsMap.lean#L96-L97

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem Formalism.HermitianLattices.Ext.L3.RankOne.conjE_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') :
    conjE φ g y = φ (g (φ.symm y)) := by sorry
