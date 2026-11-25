-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinB_locF_span_consBasis
-- name    : Formalism.HermitianLattices.Ext.L3.PinB.locF_span_consBasis
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:03.652162+00:00
-- url     : https://prove2.me/theorems/0b5ba9f6-bf6f-5689-824b-37f6dbef13cc
-- title:
--   Pin B: loc F span cons Basis
-- statement:
--   The Pin B construction uses the loc F span cons Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocFSpanConsBasis.lean#L53-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocFSpanConsBasis.lean#L53-L102

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocFEqLocFAdjoinCut
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EqBlockOfFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsExactLift
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RedEqOfSubMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocFSpanConsBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinB
open idealPowerSpanBounds integralBasisSpans
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
omit [FiniteDimensional K V] [FiniteDimensional K V']

theorem Formalism.HermitianLattices.Ext.L3.PinB.locF_span_consBasis (S : VecSplit h h') {κ : Type} (b' : Basis κ K V')
    {T : Submodule (𝓞 K) V'} (hbT : ∀ i, b' i ∈ T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hb' : locF 𝔭 (spanO b') = locF 𝔭 T) :
    locF 𝔭 (spanO (consBasis S b')) = locF 𝔭 (S.adjoin T) := by sorry
