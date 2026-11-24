-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mk_form_iff
-- name    : Formalism.HermitianLattices.Ext.L3.HU.mk_form_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:26.628374+00:00
-- url     : https://prove2.me/theorems/6d05ab03-8582-4bd6-985a-be7beb39bda1
-- title:
--   HU: mk form iff
-- statement:
--   The HU construction uses the mk form iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeMapMk.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeMapMk.lean#L37-L40

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

theorem Formalism.HermitianLattices.Ext.L3.HU.mk_form_iff (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H Y : Matrix κ κ (𝓞 K)) :
    (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))ᴴ * Hq H 𝔭 k * Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) =
      Hq H 𝔭 k ↔ ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k := by sorry
