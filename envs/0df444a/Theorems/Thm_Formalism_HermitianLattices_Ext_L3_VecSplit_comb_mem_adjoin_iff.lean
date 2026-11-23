-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_mem_adjoin_iff
-- name    : Formalism.HermitianLattices.Ext.L3.VecSplit.comb_mem_adjoin_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:32.444774+00:00
-- url     : https://prove2.me/theorems/2a9eaff4-d2d3-4984-aba2-f1560875a838
-- title:
--   Vec Split: comb mem adjoin iff
-- statement:
--   The Vec Split construction uses the comb mem adjoin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L301-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L301-L310

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
open Formalism.HermitianLattices.Ext.L3.VecSplit
variable (S : VecSplit h h')

theorem Formalism.HermitianLattices.Ext.L3.VecSplit.comb_mem_adjoin_iff (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ S.adjoin L' ↔ c ∈ (1 : Submodule (𝓞 K) K) ∧ a ∈ L' := by sorry
