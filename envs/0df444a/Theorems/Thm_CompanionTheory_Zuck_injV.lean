-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_injV
-- name    : CompanionTheory.Zuck.injV
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:34:59.590187+00:00
-- url     : https://prove2.me/theorems/cff4df84-8b10-4b79-864a-da65befc879f
-- title:
--   Zuck: inj V
-- statement:
--   The Zuck construction uses the inj V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L176-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L176-L185

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

theorem CompanionTheory.Zuck.injV (S : Steps) (Lb : Lib t) (b : Bool) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) < h) :
    ∃ T : {s // IsHCParam (shift b μ s)} → URep k r, (∀ s, (T s).R.IsDS ε (shift b μ s)) ∧
      JInj (N := M) IsHom (vr k r b, U) (fun s => one (T s)) ∧
      ∀ s, ∃ p, IsHom (vr k r b, U) (one (T s)) p ∧ p ≠ 0 := by sorry
