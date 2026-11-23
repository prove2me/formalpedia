-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
-- name    : CompanionTheory.ThKR.LL.Intw.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:22.88129+00:00
-- url     : https://prove2.me/theorems/1805849a-1e0f-4f96-8d1c-2ac1eedb237c
-- title:
--   Intw: mul
-- statement:
--   The Intw construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L24-L25

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem CompanionTheory.ThKR.LL.Intw.mul {S T : Sch l →L[ℂ] Sch l} {p q p' q' p'' q'' : Eu l} (hS : Intw S p' q' p'' q'') (hT : Intw T p q p' q') :
    Intw (S * T) p q p'' q'' := by sorry
