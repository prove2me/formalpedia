-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_isIntegralLat_adjoin
-- name    : Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.isIntegralLat_adjoin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:27:56.169009+00:00
-- url     : https://prove2.me/theorems/f0ff3d61-2f20-4f16-bb15-2e9a7412ad03
-- title:
--   Localized Fibre Sets: is Integral Lat adjoin
-- statement:
--   The Localized Fibre Sets construction uses the is Integral Lat adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/InvMemLocROfUnimod.lean#L136-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/InvMemLocROfUnimod.lean#L136-L147

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.isIntegralLat_adjoin (hs : h.IsSymm) (S : VecSplit h h')
    (hn : h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K)) {L' : Submodule (𝓞 K) V'}
    (hL' : Formalism.HermitianLatticesTheory.IsIntegralLat h' L') : Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') := by sorry
