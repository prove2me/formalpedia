-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_card_sigma_succ
-- name    : Formalism.HermitianLattices.Ext.L3.HU.card_sigma_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:32.144246+00:00
-- url     : https://prove2.me/theorems/f573bb3e-149c-4e1d-9069-82b5c0b23dd0
-- title:
--   HU: card sigma succ
-- statement:
--   The HU construction uses the card sigma succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSkewValue.lean#L142-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSkewValue.lean#L142-L177

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

theorem Formalism.HermitianLattices.Ext.L3.HU.card_sigma_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H E₀ : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) {d : 𝓞 F} {e : ℕ} (hd : d ∉ 𝔭 ^ (e + 1))
    (hHE : H * E₀ = algebraMap (𝓞 F) (𝓞 K) d • (1 : Matrix κ κ (𝓞 K))) {j : ℕ} (hj : e ≤ j) :
    Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1)) //
        Hq H 𝔭 (j + 1) * Y + Yᴴ * Hq H 𝔭 (j + 1) = 0} =
      Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) *
        Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) // Hq H 𝔭 j * Y + Yᴴ * Hq H 𝔭 j = 0} := by sorry
