-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_det_one_add_sub_mem
-- name    : Formalism.L2.SG.Pf.discriminantNormShapes.det_one_add_sub_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:22.476262+00:00
-- url     : https://prove2.me/theorems/287d11f8-c936-5893-b1f3-7611f385dceb
-- title:
--   discriminant Norm Shapes: det one add sub mem
-- statement:
--   The discriminant Norm Shapes construction uses the det one add sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscOntoOfShape.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscOntoOfShape.lean#L27-L36

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

theorem Formalism.L2.SG.Pf.discriminantNormShapes.det_one_add_sub_mem {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    {I : Ideal R} {N : Matrix n n R} (hN : ∀ i j, N i j ∈ I) : (1 + N).det - 1 ∈ I := by sorry
