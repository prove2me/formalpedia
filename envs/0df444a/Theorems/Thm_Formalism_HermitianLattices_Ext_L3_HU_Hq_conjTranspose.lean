-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Hq_conjTranspose
-- name    : Formalism.HermitianLattices.Ext.L3.HU.Hq_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:05.894771+00:00
-- url     : https://prove2.me/theorems/bf75bc73-a893-47e3-9d55-8009d0e0239d
-- title:
--   HU: Hq conj Transpose
-- statement:
--   The HU construction uses the Hq conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSkewValue.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSkewValue.lean#L92-L95

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
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
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable [Fact (IsFixF K F)]

theorem Formalism.HermitianLattices.Ext.L3.HU.Hq_conjTranspose {H : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (Hq H 𝔭 k)ᴴ = Hq H 𝔭 k := by sorry
