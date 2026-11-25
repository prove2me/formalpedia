-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_tendsto_err
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.tendsto_err
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:03:01.79808+00:00
-- url     : https://prove2.me/theorems/66585e8e-4801-551c-81f8-88e7d569405e
-- title:
--   Box Sum: tendsto err
-- statement:
--   The Box Sum construction uses the tendsto err property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoSumOfMean.lean#L72-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoSumOfMean.lean#L72-L87

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeBotOfIsMaximal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumOfMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.tendsto_err (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (A B : ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) :
    Tendsto (fun k : ℕ => A * ∑ 𝔭 ∈ S, B / (Ideal.absNorm 𝔭.1 : ℝ) ^ (k + 1 - c 𝔭)) atTop (𝓝 0) := by sorry
