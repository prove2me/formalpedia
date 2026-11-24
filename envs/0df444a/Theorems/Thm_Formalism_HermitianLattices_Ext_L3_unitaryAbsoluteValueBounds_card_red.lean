-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_card_red
-- name    : Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.card_red
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:58.407198+00:00
-- url     : https://prove2.me/theorems/0b32d499-bb7e-46d6-b20e-f496769455af
-- title:
--   unitary Absolute Value Bounds: card red
-- statement:
--   The unitary Absolute Value Bounds construction uses the card red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L88-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L88-L114

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
open NormLifting
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.card_red (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (j M : ℕ) (T : (Fin M → AQ K 𝔭 j) → Prop) :
    Nat.card {y : Fin M → AQ K 𝔭 (j + 1) //
        T fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i)} =
      Ideal.absNorm 𝔭 ^ (2 * M) * Nat.card {y // T y} := by sorry
