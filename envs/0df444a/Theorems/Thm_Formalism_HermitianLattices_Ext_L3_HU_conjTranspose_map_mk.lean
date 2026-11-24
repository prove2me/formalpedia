-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_conjTranspose_map_mk
-- name    : Formalism.HermitianLattices.Ext.L3.HU.conjTranspose_map_mk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:18.143988+00:00
-- url     : https://prove2.me/theorems/f01e5460-aa97-4c6a-8968-32e2363e250c
-- title:
--   HU: conj Transpose map mk
-- statement:
--   The HU construction uses the conj Transpose map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeMapMk.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeMapMk.lean#L23-L25

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
variable [Fact (IsFixF K F)]

theorem Formalism.HermitianLattices.Ext.L3.HU.conjTranspose_map_mk (𝔭 : Ideal (𝓞 F)) (k : ℕ) (Y : Matrix κ κ (𝓞 K)) :
    (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))ᴴ = Yᴴ.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by sorry
