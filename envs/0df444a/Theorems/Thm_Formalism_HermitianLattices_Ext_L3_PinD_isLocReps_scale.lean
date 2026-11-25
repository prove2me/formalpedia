-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinD_isLocReps_scale
-- name    : Formalism.HermitianLattices.Ext.L3.PinD.isLocReps_scale
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:35:05.322864+00:00
-- url     : https://prove2.me/theorems/5df329fd-b1b9-43dd-b661-a6d1f700e0c4
-- title:
--   Pin D: is Loc Reps scale
-- statement:
--   The Pin D construction uses the is Loc Reps scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsTotPosDefOfSmul.lean#L158-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsTotPosDefOfSmul.lean#L158-L178

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealSmulLeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocFSpanConsBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsTotPosDefOfSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinD
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.PinD.isLocReps_scale (hF : IsFixF K F) {c : 𝓞 F} (hc : algebraMap F K (c : F) ≠ 0)
    (S : VecSplit (algebraMap F K (c : F) • h) (algebraMap F K (c : F) • h'))
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s : Finset (Submodule (𝓞 K) V')}
    (hr : IsLocReps (unscale hc S) L 𝔭 s) : IsLocReps S L 𝔭 s := by sorry
