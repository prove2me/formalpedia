-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_exists_div_sq
-- name    : Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.exists_div_sq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:02:34.99753+00:00
-- url     : https://prove2.me/theorems/c5825905-7897-430a-9319-40f2546bf1a6
-- title:
--   unitary Absolute Value Bounds: exists div sq
-- statement:
--   The unitary Absolute Value Bounds construction uses the exists div sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/UnitaryDensityFieldFurther.lean#L220-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/UnitaryDensityFieldFurther.lean#L220-L224

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldMore
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther
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
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.exists_div_sq {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {w : ℕ}
    (hvn : vF 𝔭 n = w + 2) {N : ℕ} (hN : w + 3 ≤ N) :
    ∃ ϖ ∈ 𝔭, ϖ ∉ 𝔭 ^ 2 ∧ ∃ n' : 𝓞 F, n' ≠ 0 ∧ vF 𝔭 n' = w ∧ n - ϖ ^ 2 * n' ∈ 𝔭 ^ N := by sorry
