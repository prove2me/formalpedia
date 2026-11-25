-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_fibreCountingData_exists_mk_iff
-- name    : Formalism.L2.SG.Pf.fibreCountingData.exists_mk_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:15.084742+00:00
-- url     : https://prove2.me/theorems/eed5c5e8-5089-5aba-80a0-a52fa67c2ecc
-- title:
--   fibre Counting Data: exists mk iff
-- statement:
--   The fibre Counting Data construction uses the exists mk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CondZIff.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CondZIff.lean#L25-L36

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

theorem Formalism.L2.SG.Pf.fibreCountingData.exists_mk_iff {d : 𝓞 F} (hd : d ≠ 0) (hk : vF 𝔭 d ≤ k) (z : 𝓞 K) :
    (∃ w : 𝓞 K ⧸ extP K 𝔭 ^ k, mk z = w * mk (ι d)) ↔ jK z / jK (ι d) ∈ HU.SP K 𝔭 := by sorry
