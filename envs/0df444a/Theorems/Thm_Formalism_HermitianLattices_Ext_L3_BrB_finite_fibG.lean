-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrB_finite_fibG
-- name    : Formalism.HermitianLattices.Ext.L3.BrB.finite_fibG
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:18:20.535148+00:00
-- url     : https://prove2.me/theorems/13efd833-287a-4312-9e52-991f8c025a49
-- title:
--   Br B: finite fib G
-- statement:
--   The Br B construction uses the finite fib G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocReps.lean#L46-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocReps.lean#L46-L63

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocReps
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrB
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.BrB.finite_fibG (hs : h.IsSymm) (hd : IsTotPosDef h) (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {Λ' : Submodule (𝓞 K) V'} (hΛ' : Submodule.IsLattice K Λ') : (fibG S L Λ').Finite := by sorry
