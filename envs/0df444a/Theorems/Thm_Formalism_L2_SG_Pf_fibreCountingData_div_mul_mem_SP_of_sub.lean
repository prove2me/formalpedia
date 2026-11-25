-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_fibreCountingData_div_mul_mem_SP_of_sub
-- name    : Formalism.L2.SG.Pf.fibreCountingData.div_mul_mem_SP_of_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:10.655843+00:00
-- url     : https://prove2.me/theorems/a5171748-3e11-44a9-9472-e8e05b7164a1
-- title:
--   fibre Counting Data: div mul mem SP of sub
-- statement:
--   The fibre Counting Data construction uses the div mul mem SP of sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DivMulMemSPOfSub.lean#L74-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DivMulMemSPOfSub.lean#L74-L84

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscEquiv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapes
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DivMulMemSPOfSub
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

theorem Formalism.L2.SG.Pf.fibreCountingData.div_mul_mem_SP_of_sub {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d d' : 𝓞 F} (hd : d ≠ 0)
    (hd' : d' ≠ 0) {z w : 𝓞 K} {k : ℕ} (hk : vF 𝔭 d + vF 𝔭 d' ≤ k)
    (h : z - w * (ι d * ι d') ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK z / (jK (ι d) * jK (ι d')) ∈ HU.SP K 𝔭 := by sorry
