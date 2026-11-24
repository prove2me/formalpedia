-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mulVec_mem
-- name    : Formalism.HermitianLattices.Ext.L3.HU.mulVec_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:49.957175+00:00
-- url     : https://prove2.me/theorems/ee964297-4cd0-4b81-817d-337e20e33d73
-- title:
--   HU: mul Vec mem
-- statement:
--   The HU construction uses the mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EquivFunEquivOfMatrixSymm.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EquivFunEquivOfMatrixSymm.lean#L112-L114

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
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

theorem Formalism.HermitianLattices.Ext.L3.HU.mulVec_mem {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {G : Matrix κ κ K} (hG : Ent (SP K 𝔭) G) {v : κ → K}
    (hv : ∀ i, v i ∈ SP K 𝔭) (i : κ) : (G *ᵥ v) i ∈ SP K 𝔭 := by sorry
