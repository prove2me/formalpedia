-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_decW
-- name    : CompanionTheory.Zuck.decW
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:32:11.537617+00:00
-- url     : https://prove2.me/theorems/34451197-2d76-4e82-bcd5-dc60bd56608b
-- title:
--   Zuck: dec W
-- statement:
--   The Zuck construction uses the dec W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L236-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L236-L334

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
variable {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem CompanionTheory.Zuck.decW (S : Steps) (Lb : Lib t) (hk : 1 ≤ k) : ∀ (l : ℕ) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ},
    U.R.IsDS ε μ → GapAtLeast ε μ h → t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 + l < h →
    (∀ a c, a < c → (l : ℝ) + 1 ≤ μ a - μ c) →
    ∀ T : Sub (2 * r + k + 1) l → URep k r, (∀ I, (T I).R.IsDS ε (addSet μ I.1)) →
    ∃ io pr, IsDec (N := M) IsHom (wedge k r l, U) (fun I => one (T I)) io pr
  := by sorry
