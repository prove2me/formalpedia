-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_inI_int
-- name    : Formalism.HermitianLattices.Ext.L3.Cell.inI_int
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:42.730807+00:00
-- url     : https://prove2.me/theorems/0c61c809-4e27-44d2-982e-83be5f1102b0
-- title:
--   Cell: in I int
-- statement:
--   The Cell construction uses the in I int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CongrPIffInI.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CongrPIffInI.lean#L24-L27

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem Formalism.HermitianLattices.Ext.L3.Cell.inI_int (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {z : 𝓞 K} : InI 𝔭 k (κ z) ↔ z ∈ extP K 𝔭 ^ k := by sorry
