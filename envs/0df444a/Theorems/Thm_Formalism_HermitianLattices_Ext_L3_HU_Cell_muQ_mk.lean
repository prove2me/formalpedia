-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Cell_muQ_mk
-- name    : Formalism.HermitianLattices.Ext.L3.HU.Cell.muQ_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:37.235314+00:00
-- url     : https://prove2.me/theorems/613fe83f-44ba-43ce-9481-af45d548c61d
-- title:
--   Cell: mu Q mk
-- statement:
--   The Cell construction uses the mu Q mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryReduction.lean#L118-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryReduction.lean#L118-L119

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
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
open HermitianSublattices idealPowerSpanBounds
open Formalism.HermitianLattices.Ext.L3.HU.Cell
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.HU.Cell.muQ_mk {𝔭 : Ideal (𝓞 F)} {j : ℕ} (c : ℕ) {d : 𝓞 F} (hd : d ∈ 𝔭 ^ j) (a : 𝓞 K) :
    muQ (K := K) c hd (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (ι d * a) := by sorry
