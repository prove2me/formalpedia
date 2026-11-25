-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_isUnit_det_of_witness
-- name    : Formalism.L2.SG.Pf.discriminantNormShapes.isUnit_det_of_witness
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:41.714231+00:00
-- url     : https://prove2.me/theorems/16facbc0-7f55-45d3-b7a5-834746a0b97d
-- title:
--   discriminant Norm Shapes: is Unit det of witness
-- statement:
--   The discriminant Norm Shapes construction uses the is Unit det of witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscOntoOfShape.lean#L135-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscOntoOfShape.lean#L135-L180

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EQMulDiagQMulEQMem
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOntoOfShape
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.HermitianLattices.Ext.L3.localValuationFiltration Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.L2.SG.Pf.discriminantNormShapes.isUnit_det_of_witness {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F}
    (ha : ∀ i, a i ≠ 0) {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k)
    {Y P W : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (hWH : ∀ i j, (W * diagQ K 𝔭 k a) i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) :
    IsUnit P.det := by sorry
