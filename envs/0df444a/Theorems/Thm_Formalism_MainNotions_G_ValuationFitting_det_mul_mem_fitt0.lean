-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_det_mul_mem_fitt0
-- name    : Formalism.MainNotions.G.ValuationFitting.det_mul_mem_fitt0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:55:33.388906+00:00
-- url     : https://prove2.me/theorems/273dc60f-5733-42fc-a34d-2bbc68836840
-- title:
--   Valuation Fitting: det mul mem fitt0
-- statement:
--   The Valuation Fitting construction uses the det mul mem fitt0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/FittingIdeal/DetMulMemFitt0.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/FittingIdeal/DetMulMemFitt0.lean#L31-L34

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ValuationFitting
open ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R]

theorem Formalism.MainNotions.G.ValuationFitting.det_mul_mem_fitt0 {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) (W : Matrix (Fin h) (Fin m) R) :
    (α * W).det ∈ Formalism.L2.FormalSeriesBounds.S4.fitt0 α := by sorry
