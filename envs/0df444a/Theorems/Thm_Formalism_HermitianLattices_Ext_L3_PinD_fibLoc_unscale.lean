-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinD_fibLoc_unscale
-- name    : Formalism.HermitianLattices.Ext.L3.PinD.fibLoc_unscale
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:34.767905+00:00
-- url     : https://prove2.me/theorems/9dd22373-6858-430a-9d2a-3a85a601fcd9
-- title:
--   Pin D: fib Loc unscale
-- statement:
--   The Pin D construction uses the fib Loc unscale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsTotPosDefOfSmul.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsTotPosDefOfSmul.lean#L152-L156

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
omit [FiniteDimensional K V] [FiniteDimensional K V']

theorem Formalism.HermitianLattices.Ext.L3.PinD.fibLoc_unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V') :
    fibLoc S L 𝔭 T = fibLoc (unscale hc S) L 𝔭 T := by sorry
