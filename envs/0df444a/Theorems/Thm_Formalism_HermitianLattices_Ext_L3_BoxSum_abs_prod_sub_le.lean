-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_abs_prod_sub_le
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.abs_prod_sub_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:04:33.016012+00:00
-- url     : https://prove2.me/theorems/d69c55fa-e3ca-56c2-8946-292a30e8bbba
-- title:
--   Box Sum: abs prod sub le
-- statement:
--   The Box Sum construction uses the abs prod sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoSumOfMean.lean#L52-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoSumOfMean.lean#L52-L70

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

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.abs_prod_sub_le (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (a : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → 𝓞 F → ℝ) (C : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) (hbd : ∀ 𝔭 ∈ S, ∀ n, |a 𝔭 n| ≤ C 𝔭)
    (hcg : ∀ 𝔭 ∈ S, ∀ (n n' : 𝓞 F) (k : ℕ), n ≠ 0 → vF 𝔭.1 n + c 𝔭 ≤ k → n - n' ∈ 𝔭.1 ^ k →
      a 𝔭 n = a 𝔭 n') (k : ℕ) {n : 𝓞 F} (hn : n ≠ 0) :
    |∏ 𝔭 ∈ S, a 𝔭 n - ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n))| ≤
      2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, (if n ∈ 𝔭.1 ^ (k + 1 - c 𝔭) then 1 else 0) := by sorry
