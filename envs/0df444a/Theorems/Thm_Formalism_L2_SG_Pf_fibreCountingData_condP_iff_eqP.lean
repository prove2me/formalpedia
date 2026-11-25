-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_fibreCountingData_condP_iff_eqP
-- name    : Formalism.L2.SG.Pf.fibreCountingData.condP_iff_eqP
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:53.513868+00:00
-- url     : https://prove2.me/theorems/4b5625f6-2928-5892-a4b4-1cfe2aa6c6ec
-- title:
--   fibre Counting Data: cond P iff eq P
-- statement:
--   The fibre Counting Data construction uses the cond P iff eq P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CondZIff.lean#L80-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CondZIff.lean#L80-L96

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DivMulMemSPOfSub
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CondZIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.fibreCountingData
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsMaximal] {k : ℕ}
local notation "mk" => Ideal.Quotient.mk (extP K 𝔭 ^ k)
variable {m : ℕ} (a : Fin m → 𝓞 F)
variable {a}

theorem Formalism.L2.SG.Pf.fibreCountingData.condP_iff_eqP (ha : ∀ i, a i ≠ 0) (hk : ∀ i, vF 𝔭 (a i) ≤ k)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (∃ P, P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y.map mk) ↔
      ∀ i j, jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by sorry
