-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_pivot
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.pivot
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:53:54.892629+00:00
-- url     : https://prove2.me/theorems/5a68cde0-e183-4d8f-9f94-c9dab50039c6
-- title:
--   Pf: pivot
-- statement:
--   The Pf construction uses the pivot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/DescentCore.lean#L7-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/DescentCore.lean#L7-L43

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_DescentCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf
open Finset

theorem Formalism.MainNotions.FormalGroupSystem.Pf.pivot {K κ : Type*} [Field K] (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) (f : κ → K) (s : Finset κ) :
    (∃ k ∈ s, f k ≠ 0) → ∃ k0 ∈ s, f k0 ≠ 0 ∧ ∀ k ∈ s, f k / f k0 ∈ R := by sorry
