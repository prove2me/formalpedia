-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_prod_atP
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_prod_atP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:22.472516+00:00
-- url     : https://prove2.me/theorems/a0958e0c-7921-4490-9f2e-ff1a03123e26
-- title:
--   Gen: coeff prod at P
-- statement:
--   The Gen construction uses the coeff prod at P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L68-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L68-L99

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

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_prod_atP (g : ∀ v, MvPowerSeries (ι v) K) (n : (Σ v, ι v) →₀ ℕ) :
    MvPowerSeries.coeff n (∏ v, atP v (g v)) = ∏ v, MvPowerSeries.coeff (eqv n v) (g v) := by sorry
