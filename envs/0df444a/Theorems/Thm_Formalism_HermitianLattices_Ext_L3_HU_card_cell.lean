-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_card_cell
-- name    : Formalism.HermitianLattices.Ext.L3.HU.card_cell
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:29.611871+00:00
-- url     : https://prove2.me/theorems/be27db79-6107-40d1-bb52-f8ac22973d9d
-- title:
--   HU: card cell
-- statement:
--   The HU construction uses the card cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryReduction.lean#L128-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryReduction.lean#L128-L189

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
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable [Fact (IsFixF K F)]

theorem Formalism.HermitianLattices.Ext.L3.HU.card_cell {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {H : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H)
    {j c : ℕ} (hcj : c ≤ j)
    (hu : ∀ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)),
      Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c) → IsUnit X.det) :
    Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)) //
        Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c)} =
      Nat.card {X' : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) //
          ∃ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)), Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c) ∧
            X.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right j c))) = X'} *
        Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ c) // Hq H 𝔭 c * Y + Yᴴ * Hq H 𝔭 c = 0} := by sorry
