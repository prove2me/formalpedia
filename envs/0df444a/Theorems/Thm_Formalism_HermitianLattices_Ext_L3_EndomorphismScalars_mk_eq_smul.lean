-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_EndomorphismScalars_mk_eq_smul
-- name    : Formalism.HermitianLattices.Ext.L3.EndomorphismScalars.mk_eq_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:04.907843+00:00
-- url     : https://prove2.me/theorems/64ffc401-caf9-453c-9d96-66c2c2855a83
-- title:
--   Endomorphism Scalars: mk eq smul
-- statement:
--   The Endomorphism Scalars construction uses the mk eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SmulGenMemIff.lean#L36-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SmulGenMemIff.lean#L36-L52

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

theorem Formalism.HermitianLattices.Ext.L3.EndomorphismScalars.mk_eq_smul (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (x : ↥L) :
    ∃ a : 𝓞 K, (Submodule.Quotient.mk x : Qk L 𝔭 k) = a • Submodule.Quotient.mk ⟨e, he.1⟩ := by sorry
