-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_mul_mk_eq_zero_iff
-- name    : Formalism.L2.SG.Pf.discriminantGroupCounts.mul_mk_eq_zero_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:19.205684+00:00
-- url     : https://prove2.me/theorems/c3c1c995-c4e4-5b7f-814e-1de59f4dae40
-- title:
--   discriminant Group Counts: mul mk eq zero iff
-- statement:
--   The discriminant Group Counts construction uses the mul mk eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscriminantGroupCounts.lean#L18-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscriminantGroupCounts.lean#L18-L79

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantGroupCounts
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantGroupCounts
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.L2.SG.Pf.discriminantGroupCounts.mul_mk_eq_zero_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} {e k : ℕ}
    (ha : a ∈ 𝔭 ^ e) (ha' : a ∉ 𝔭 ^ (e + 1)) (hek : e ≤ k) (w : 𝓞 K) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) w * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι a) = 0 ↔
      w ∈ extP K 𝔭 ^ (k - e) := by sorry
