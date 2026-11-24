-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_unif_pow
-- name    : Formalism.HermitianLattices.Ext.L3.D2.nO_unif_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:41:58.164252+00:00
-- url     : https://prove2.me/theorems/d01b070a-8509-41c2-8253-3ca1a01b889b
-- title:
--   D2: n O unif pow
-- statement:
--   The D2 construction uses the n O unif pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L163-L167

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open NO

theorem Formalism.HermitianLattices.Ext.L3.D2.nO_unif_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {π : 𝓞 F} (hπ : π ∈ 𝔭) (hπ' : π ∉ 𝔭 ^ 2) (k : ℕ) :
    nO 𝔭 (algebraMap F K (π : F) ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by sorry
