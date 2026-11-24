-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_EndomorphismScalars_end_surj
-- name    : Formalism.HermitianLattices.Ext.L3.EndomorphismScalars.end_surj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:59.333515+00:00
-- url     : https://prove2.me/theorems/c43fd857-145a-4a70-907a-343b6c7f69ad
-- title:
--   Endomorphism Scalars: end surj
-- statement:
--   The Endomorphism Scalars construction uses the end surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SmulGenMemIff.lean#L95-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SmulGenMemIff.lean#L95-L103

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealLeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SmulGenMemIff
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V}

theorem Formalism.HermitianLattices.Ext.L3.EndomorphismScalars.end_surj (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ)
    (X : Module.End (𝓞 K) (Qk L 𝔭 k)) :
    ∃ b : 𝓞 K, algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b = X := by sorry
