-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_decV
-- name    : CompanionTheory.Zuck.decV
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:21:45.808011+00:00
-- url     : https://prove2.me/theorems/fd063594-c0b8-411e-9975-e416752ef9ce
-- title:
--   Zuck: dec V
-- statement:
--   The Zuck construction uses the dec V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L187-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L187-L234

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

theorem CompanionTheory.Zuck.decV (S : Steps) (Lb : Lib t) (hk : 1 ≤ k) (b : Bool) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 < h)
    (T : Fin (2 * r + k + 1) → URep k r) (hT : ∀ s, (T s).R.IsDS ε (shift b μ s)) :
    ∃ io pr, IsDec (N := M) IsHom (vr k r b, U) (fun s => one (T s)) io pr := by sorry
