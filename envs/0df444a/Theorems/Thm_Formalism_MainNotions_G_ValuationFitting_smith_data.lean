-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_smith_data
-- name    : Formalism.MainNotions.G.ValuationFitting.smith_data
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:41.32462+00:00
-- url     : https://prove2.me/theorems/7664292a-49e3-437d-abeb-42da13fdb4f2
-- title:
--   Valuation Fitting: smith data
-- statement:
--   The Valuation Fitting construction uses the smith data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/FittingIdeal/DetMulMemFitt0.lean#L71-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/FittingIdeal/DetMulMemFitt0.lean#L71-L117

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

theorem Formalism.MainNotions.G.ValuationFitting.smith_data (hv : v.Integers R) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) :
    ∃ (P : Matrix (Fin m) (Fin m) R) (Q : Matrix (Fin h) (Fin h) R) (a' : Fin m → R),
      IsUnit P.det ∧ IsUnit Q.det ∧ P * α * Q = Matrix.diagonal a' * Em R m h ∧
      (∀ j : Fin m, h ≤ (j : ℕ) → a' j = 0) ∧ ∏ j, v (algebraMap R C (a' j)) = x := by sorry
