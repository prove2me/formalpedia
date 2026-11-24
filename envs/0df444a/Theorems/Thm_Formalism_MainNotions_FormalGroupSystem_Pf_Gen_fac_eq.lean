-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_fac_eq
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.fac_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:54:03.157802+00:00
-- url     : https://prove2.me/theorems/fbb4b093-3d2c-4e54-a8f3-b9809c060b3e
-- title:
--   Gen: fac eq
-- statement:
--   The Gen construction uses the fac eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L132-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L132-L144

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

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.fac_eq [∀ v, Fintype (ι v)] (n : (Σ v, ι v) →₀ ℕ) : fac n = ∏ v, fac (eqv n v) := by sorry
