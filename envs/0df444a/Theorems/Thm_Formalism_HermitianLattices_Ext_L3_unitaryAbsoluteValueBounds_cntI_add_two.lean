-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cntI_add_two
-- name    : Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.cntI_add_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:20.270855+00:00
-- url     : https://prove2.me/theorems/f3f6a4f5-fd4d-4520-b5f5-6441ebbceae8
-- title:
--   unitary Absolute Value Bounds: cnt I add two
-- statement:
--   The unitary Absolute Value Bounds construction uses the cnt I add two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L116-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean#L116-L134

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

theorem Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.cntI_add_two (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) (h2 : ϖ ∉ 𝔭 ^ 2) (j M : ℕ) {n n' : 𝓞 K}
    (hn : n - ι ϖ ^ 2 * n' ∈ extP K 𝔭 ^ (j + 2)) :
    cntI hF 𝔭 (j + 2) M n = Ideal.absNorm 𝔭 ^ (2 * M) * cnt hF 𝔭 j M n' := by sorry
