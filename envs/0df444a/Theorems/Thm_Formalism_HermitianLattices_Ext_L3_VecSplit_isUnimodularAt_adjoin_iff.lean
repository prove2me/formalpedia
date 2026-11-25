-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_isUnimodularAt_adjoin_iff
-- name    : Formalism.HermitianLattices.Ext.L3.VecSplit.isUnimodularAt_adjoin_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:22.582516+00:00
-- url     : https://prove2.me/theorems/bbd954db-004d-5630-9793-72561de4de5c
-- title:
--   Vec Split: is Unimodular At adjoin iff
-- statement:
--   The Vec Split construction uses the is Unimodular At adjoin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L395-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L395-L397

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

theorem Formalism.HermitianLattices.Ext.L3.VecSplit.isUnimodularAt_adjoin_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (S : VecSplit h h')
    (h1 : h S.x₀ S.x₀ = 1) (L' : Submodule (𝓞 K) V') (p : Ideal (𝓞 K)) (hp : p.IsMaximal) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h' p L' := by sorry
