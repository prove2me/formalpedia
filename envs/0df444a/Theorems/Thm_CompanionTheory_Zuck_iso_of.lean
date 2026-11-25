-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_iso_of
-- name    : CompanionTheory.Zuck.iso_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:14.353007+00:00
-- url     : https://prove2.me/theorems/b2546782-a485-5d49-bfa9-d9a21e6b8d61
-- title:
--   Zuck: iso of
-- statement:
--   The Zuck construction uses the iso of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L171-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L171-L174

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

theorem CompanionTheory.Zuck.iso_of (S : Steps) (Lb : Lib t) {μ : Fin (2 * r + k + 1) → ℝ} {U U' : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hU' : U'.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε < h) :
    IsIso (N := M) IsHom (one U) (one U') := by sorry
