-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_map_smul_hermL
-- name    : Formalism.HermitianLattices.Ext.L3.D2.J.map_smul_hermL
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:54:29.105686+00:00
-- url     : https://prove2.me/theorems/16e64ec4-a94c-4e8b-989e-0bbd52320a23
-- title:
--   J: map smul herm L
-- statement:
--   The J construction uses the map smul herm L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqMapMulKer.lean#L123-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqMapMulKer.lean#L123-L155

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

theorem Formalism.HermitianLattices.Ext.L3.D2.J.map_smul_hermL (A : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0)
    (hδ1 : δ ∈ pK K 𝔭 0) (hδ2 : δ⁻¹ ∈ pK K 𝔭 0) :
    (hermL A 𝔭 k).map (DistribSMul.toAddMonoidHom (V →ₗ⋆[K] V →ₗ[K] K) δ) =
      sesqL A 𝔭 k ⊓ (symF (K := K) (V := V)).ker := by sorry
