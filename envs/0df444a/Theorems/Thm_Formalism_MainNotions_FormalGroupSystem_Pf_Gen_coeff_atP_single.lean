-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_atP_single
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_atP_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:05.077816+00:00
-- url     : https://prove2.me/theorems/2a637ae5-f776-4303-a78d-df501d932251
-- title:
--   Gen: coeff at P single
-- statement:
--   The Gen construction uses the coeff at P single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L53-L58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
variable {K Pl : Type} [CommRing K] {ι : Pl → Type}
variable [Fintype Pl]
variable [DecidableEq Pl]

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_atP_single (v : Pl) (f : MvPowerSeries (ι v) K) (m : ι v →₀ ℕ) :
    MvPowerSeries.coeff (eqv.symm (Pi.single v m)) (atP v f) = MvPowerSeries.coeff m f := by sorry
