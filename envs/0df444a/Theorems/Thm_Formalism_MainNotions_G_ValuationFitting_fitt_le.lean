-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_fitt_le
-- name    : Formalism.MainNotions.G.ValuationFitting.fitt_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:56:38.265915+00:00
-- url     : https://prove2.me/theorems/394909a4-af94-4ff3-8a1d-e6c89654767e
-- title:
--   Valuation Fitting: fitt le
-- statement:
--   The Valuation Fitting construction uses the fitt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/FittingIdeal/DetMulMemFitt0.lean#L138-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/FittingIdeal/DetMulMemFitt0.lean#L138-L157

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
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem Formalism.MainNotions.G.ValuationFitting.fitt_le (hv : v.Integers R) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) :
    ∀ g : Fin m → Fin h, v (algebraMap R C (α.submatrix id g).det) ≤ x := by sorry
