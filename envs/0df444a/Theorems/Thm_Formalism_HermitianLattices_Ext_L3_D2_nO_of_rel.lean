-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_of_rel
-- name    : Formalism.HermitianLattices.Ext.L3.D2.nO_of_rel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:48:25.44052+00:00
-- url     : https://prove2.me/theorems/2e5532c4-20d3-425d-8645-d6f772e5fef9
-- title:
--   D2: n O of rel
-- statement:
--   The D2 construction uses the n O of rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L145-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L145-L176

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
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
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.D2.nO_of_rel (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {D s : 𝓞 F} (hD0 : D ≠ 0) (hs𝔭 : s ∉ 𝔭) {G : K}
    (hrel : algebraMap (𝓞 K) K (ι D) = algebraMap (𝓞 K) K (ι s) * G) :
    G ∈ pK K 𝔭 0 ∧ G ≠ 0 ∧ nO 𝔭 G = Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 D) := by sorry
