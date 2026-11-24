-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_skew_value
-- name    : Formalism.HermitianLattices.Ext.L3.HU.exists_skew_value
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:47.286259+00:00
-- url     : https://prove2.me/theorems/c4263678-b87c-4f88-bf3a-49e2eaa237c5
-- title:
--   HU: exists skew value
-- statement:
--   The HU construction uses the exists skew value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSkewValue.lean#L97-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSkewValue.lean#L97-L140

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

theorem Formalism.HermitianLattices.Ext.L3.HU.exists_skew_value (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H E₀ : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) {d : 𝓞 F} {e : ℕ} (hd : d ∉ 𝔭 ^ (e + 1))
    (hHE : H * E₀ = algebraMap (𝓞 F) (𝓞 K) d • (1 : Matrix κ κ (𝓞 K))) {j : ℕ} (hj : e ≤ j)
    (S : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1))) (hS : S ∈ hermSub κ (RingHom.ker (piQ K 𝔭 j))) :
    ∃ Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1)),
      Hq H 𝔭 (j + 1) * Y + Yᴴ * Hq H 𝔭 (j + 1) = S := by sorry
