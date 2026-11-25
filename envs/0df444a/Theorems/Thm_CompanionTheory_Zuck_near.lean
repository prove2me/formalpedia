-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_near
-- name    : CompanionTheory.Zuck.near
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:38:15.660255+00:00
-- url     : https://prove2.me/theorems/d5a012b6-711e-4954-b351-d72f147a2cfb
-- title:
--   Zuck: near
-- statement:
--   The Zuck construction uses the near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L132-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L132-L150

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)
variable {n : ℕ}

theorem CompanionTheory.Zuck.near {ε : Fin n → Bool} {μ : Fin n → ℝ} {h D : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hD : ∀ a c, a < c → D ≤ μ a - μ c) {ν : Fin n → ℝ} (j : ℕ) (hj : (j : ℝ) < D)
    (hx : ∀ a, ∃ x : ℕ, x ≤ j ∧ ν a = μ a + x) :
    IsHCParam ν ∧ GapAtLeast ε ν (h - j) ∧ ∀ a c, a < c → D - j ≤ ν a - ν c := by sorry
