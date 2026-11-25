-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrB_alphaL_gmap
-- name    : Formalism.HermitianLattices.Ext.L3.BrB.alphaL_gmap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:04:34.964427+00:00
-- url     : https://prove2.me/theorems/0400299d-9bb7-5e59-89cc-2fff0c326047
-- title:
--   Br B: alpha L gmap
-- statement:
--   The Br B construction uses the alpha L gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumLocRepsEq.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumLocRepsEq.lean#L57-L60

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumLocRepsEq
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
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.BrB.alphaL_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : alphaL h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 = alphaL h T 𝔭 := by sorry
