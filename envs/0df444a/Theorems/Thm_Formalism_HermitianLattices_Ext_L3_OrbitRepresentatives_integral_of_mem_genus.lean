-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbitRepresentatives_integral_of_mem_genus
-- name    : Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives.integral_of_mem_genus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:13.73818+00:00
-- url     : https://prove2.me/theorems/2c18b6d3-295c-4dd5-9975-eae93497a1ea
-- title:
--   Orbit Representatives: integral of mem genus
-- statement:
--   The Orbit Representatives construction uses the integral of mem genus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardStabilizerAutSub.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardStabilizerAutSub.lean#L70-L74

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinMemGenusIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
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
open Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives.integral_of_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n) (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h L := by sorry
