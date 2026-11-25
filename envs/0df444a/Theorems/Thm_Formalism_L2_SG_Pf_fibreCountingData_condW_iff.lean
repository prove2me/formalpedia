-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_fibreCountingData_condW_iff
-- name    : Formalism.L2.SG.Pf.fibreCountingData.condW_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:00.382052+00:00
-- url     : https://prove2.me/theorems/3ebf3e1b-d0e6-542c-b0b4-bf8469df8b82
-- title:
--   fibre Counting Data: cond W iff
-- statement:
--   The fibre Counting Data construction uses the cond W iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CondZIff.lean#L109-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CondZIff.lean#L109-L126

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

theorem Formalism.L2.SG.Pf.fibreCountingData.condW_iff (ha : ∀ i, a i ≠ 0) (hk : ∀ i j, vF 𝔭 (a i) + vF 𝔭 (a j) ≤ k)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (∃ W, (Y.map mk)ᴴ * diagQ K 𝔭 k a * Y.map mk - diagQ K 𝔭 k a =
        diagQ K 𝔭 k a * W * diagQ K 𝔭 k a) ↔
      ∀ i j, jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) ∈ HU.SP K 𝔭 := by sorry
