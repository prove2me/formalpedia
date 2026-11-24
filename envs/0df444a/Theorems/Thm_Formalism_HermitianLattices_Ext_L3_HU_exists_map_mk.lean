-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_map_mk
-- name    : Formalism.HermitianLattices.Ext.L3.HU.exists_map_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:28.55658+00:00
-- url     : https://prove2.me/theorems/ab5509bc-9f58-4d4c-9975-9a62061d2f11
-- title:
--   HU: exists map mk
-- statement:
--   The HU construction uses the exists map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeMapMk.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeMapMk.lean#L53-L56

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

theorem Formalism.HermitianLattices.Ext.L3.HU.exists_map_mk (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    ∃ Y : Matrix κ κ (𝓞 K), Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = X := by sorry
