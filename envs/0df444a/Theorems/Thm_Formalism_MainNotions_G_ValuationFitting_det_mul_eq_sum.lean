-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_det_mul_eq_sum
-- name    : Formalism.MainNotions.G.ValuationFitting.det_mul_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:51.373607+00:00
-- url     : https://prove2.me/theorems/9f241fc0-6bf9-4ed4-b0df-03d8871c9a7e
-- title:
--   Valuation Fitting: det mul eq sum
-- statement:
--   The Valuation Fitting construction uses the det mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/FittingIdeal/DetMulMemFitt0.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/FittingIdeal/DetMulMemFitt0.lean#L19-L29

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

theorem Formalism.MainNotions.G.ValuationFitting.det_mul_eq_sum {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) (W : Matrix (Fin h) (Fin m) R) :
    (α * W).det = ∑ f : Fin m → Fin h, (∏ i, W (f i) i) * (α.submatrix id f).det := by sorry
