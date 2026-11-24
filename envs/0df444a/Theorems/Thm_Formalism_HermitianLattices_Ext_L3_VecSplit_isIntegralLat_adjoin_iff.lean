-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_isIntegralLat_adjoin_iff
-- name    : Formalism.HermitianLattices.Ext.L3.VecSplit.isIntegralLat_adjoin_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:17.660596+00:00
-- url     : https://prove2.me/theorems/f70faa2d-fb14-4247-b785-a13b62d1adc7
-- title:
--   Vec Split: is Integral Lat adjoin iff
-- statement:
--   The Vec Split construction uses the is Integral Lat adjoin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L391-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L391-L393

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.VecSplit.isIntegralLat_adjoin_iff (hs : h.IsSymm) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1)
    (L' : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsIntegralLat h' L' := by sorry
