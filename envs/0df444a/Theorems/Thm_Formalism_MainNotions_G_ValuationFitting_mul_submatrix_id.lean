-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_mul_submatrix_id
-- name    : Formalism.MainNotions.G.ValuationFitting.mul_submatrix_id
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:10.815904+00:00
-- url     : https://prove2.me/theorems/ee903c92-1a31-4eab-b871-e7258e906d5e
-- title:
--   Valuation Fitting: mul submatrix id
-- statement:
--   The Valuation Fitting construction uses the mul submatrix id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/FittingIdeal/DetMulMemFitt0.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/FittingIdeal/DetMulMemFitt0.lean#L36-L39

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

theorem Formalism.MainNotions.G.ValuationFitting.mul_submatrix_id {a b c e : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin c) R)
    (g : Fin e → Fin c) : (A * B).submatrix id g = A * B.submatrix id g := by sorry
