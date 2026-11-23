-- Prove2me | Theorems.Thm_Formalism_BehrendSets_E3_core
-- name    : Formalism.BehrendSets.E3.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:45.426443+00:00
-- url     : https://prove2.me/theorems/84b5f25d-1b7f-4865-b8af-5f823d7cc385
-- title:
--   E3: core
-- statement:
--   The E3 construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/SpaceFreeOfBehrendFree.lean#L24-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/SpaceFreeOfBehrendFree.lean#L24-L81

import Definitions.Def_Formalism_BehrendSets_StatementE
import Mathlib
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_MulAbsSubLt
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_SpaceFreeOfBehrendFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.E3

theorem Formalism.BehrendSets.E3.core {n Lw : ℕ} [NeZero n] {S : Finset ℕ} (hS : ∀ s ∈ S, 4 * Lw * s < n)
    (hF : SpaceFreePos Lw S) {h u t : ZMod n} (hord : Lw < addOrderOf h) {i₁ i₂ i₃ : ℤ}
    (h12 : i₁ < i₂) (h23 : i₂ < i₃) (hw : i₃ - i₁ ≤ (Lw : ℤ))
    (m₁ : t + i₁ • h ∈ thick n S u) (m₂ : t + i₂ • h ∈ thick n S u)
    (m₃ : t + i₃ • h ∈ thick n S u) : False := by sorry
