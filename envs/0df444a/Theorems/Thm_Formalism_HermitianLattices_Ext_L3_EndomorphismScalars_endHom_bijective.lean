-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_EndomorphismScalars_endHom_bijective
-- name    : Formalism.HermitianLattices.Ext.L3.EndomorphismScalars.endHom_bijective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:31.552011+00:00
-- url     : https://prove2.me/theorems/daa2ebb5-14ef-472d-84d9-dfe27db6b91a
-- title:
--   Endomorphism Scalars: end Hom bijective
-- statement:
--   The Endomorphism Scalars construction uses the end Hom bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SmulGenMemIff.lean#L129-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SmulGenMemIff.lean#L129-L139

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

theorem Formalism.HermitianLattices.Ext.L3.EndomorphismScalars.endHom_bijective (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) :
    Function.Bijective (endHom h𝔭 he k) := by sorry
