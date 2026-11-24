-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_nO_prod
-- name    : Formalism.HermitianLattices.Ext.L3.D2.J.nO_prod
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:54:15.320293+00:00
-- url     : https://prove2.me/theorems/d22dc8a0-6096-43b1-8157-2b0b22fc0c8c
-- title:
--   J: n O prod
-- statement:
--   The J construction uses the n O prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqMapMulKer.lean#L169-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqMapMulKer.lean#L169-L177

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
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
open Formalism.HermitianLattices.Ext.L3.D2.J

theorem Formalism.HermitianLattices.Ext.L3.D2.J.nO_prod {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ι : Type} (s : Finset ι) (z : ι → K)
    (hz : ∀ i, z i ∈ pK K 𝔭 0 ∧ z i ≠ 0) :
    (∏ i ∈ s, z i) ∈ pK K 𝔭 0 ∧ nO 𝔭 (∏ i ∈ s, z i) = ∏ i ∈ s, nO 𝔭 (z i) := by sorry
