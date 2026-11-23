-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_exists_approx
-- name    : CompanionTheory.D.gk.admitted.PrismTransfer.exists_approx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:17.610798+00:00
-- url     : https://prove2.me/theorems/329a39dc-3533-4523-b9b0-3e0d215836e1
-- title:
--   Prism Transfer: exists approx
-- statement:
--   The Prism Transfer construction uses the exists approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L159-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L159-L174

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Kronecker Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.PrismTransfer
variable {G : Type} [Group G] {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
variable [TopologicalSpace G] {st : G → G} {S : Set G} {ρ : G →* Matrix ι ι ℂ} {ρ' : G →* Matrix ι' ι' ℂ}

theorem CompanionTheory.D.gk.admitted.PrismTransfer.exists_approx (h : IsGood st S ρ) (hi : Function.Injective ρ) {C : Set G} (hC : IsCompact C)
    {Φ : G → ℂ} (hΦ : Continuous Φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (τ : G →* Matrix κ κ ℂ) (a b : κ → ℂ),
      IsGood st S τ ∧ ∀ x ∈ C, ‖Φ x - a ⬝ᵥ (τ x *ᵥ b)‖ ≤ δ := by sorry
