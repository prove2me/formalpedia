-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unif_pow_mem_pK_zero
-- name    : Formalism.HermitianLattices.Ext.L3.D2.unif_pow_mem_pK_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:33:39.340543+00:00
-- url     : https://prove2.me/theorems/284b3b69-9275-449d-873f-233d43314780
-- title:
--   D2: unif pow mem p K zero
-- statement:
--   The D2 construction uses the unif pow mem p K zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsEquivOfMemEndL.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsEquivOfMemEndL.lean#L89-L96

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
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

theorem Formalism.HermitianLattices.Ext.L3.D2.unif_pow_mem_pK_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ : π ∈ 𝔭) (k : ℕ) :
    algebraMap F K (π : F) ^ k ∈ pK K 𝔭 0 := by sorry
