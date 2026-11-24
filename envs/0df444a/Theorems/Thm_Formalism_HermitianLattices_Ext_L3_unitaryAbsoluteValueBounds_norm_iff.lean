-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_norm_iff
-- name    : Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.norm_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:25.644295+00:00
-- url     : https://prove2.me/theorems/a5472972-a04d-4aa0-b64c-90ee20082844
-- title:
--   unitary Absolute Value Bounds: norm iff
-- statement:
--   The unitary Absolute Value Bounds construction uses the norm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L53-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L53-L86

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

theorem Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.norm_iff (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭)
    (h2 : ϖ ∉ 𝔭 ^ 2) (j : ℕ) {M : ℕ} {n n' : 𝓞 K} (hn : n - ι ϖ ^ 2 * n' ∈ extP K 𝔭 ^ (j + 2))
    (y : Fin M → AQ K 𝔭 (j + 1)) :
    ∑ i, sg hF 𝔭 (j + 2) (mulW 𝔭 (map_mem h1) j (y i)) * mulW 𝔭 (map_mem h1) j (y i) =
        Ideal.Quotient.mk _ n ↔
      ∑ i, sg hF 𝔭 j (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i)) *
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i) =
        Ideal.Quotient.mk _ n' := by sorry
