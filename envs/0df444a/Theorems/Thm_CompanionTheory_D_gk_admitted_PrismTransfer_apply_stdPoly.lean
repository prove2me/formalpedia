-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_apply_stdPoly
-- name    : CompanionTheory.D.gk.admitted.PrismTransfer.apply_stdPoly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:17.863197+00:00
-- url     : https://prove2.me/theorems/787731cb-e524-42c0-966a-bfe5a7cad3df
-- title:
--   Prism Transfer: apply std Poly
-- statement:
--   The Prism Transfer construction uses the apply std Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L259-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L259-L264

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

theorem CompanionTheory.D.gk.admitted.PrismTransfer.apply_stdPoly {G V : Type} [AddCommGroup V] [Module ℂ V] (τ : G → Module.End ℂ V) (E : Module.End ℂ V)
    {M : ℕ} (g : Fin M → G) (ℓ : V →ₗ[ℂ] ℂ) (u : V) :
    ℓ (stdPoly E (fun i => τ (g i)) u) = ∑ π : Equiv.Perm (Fin M),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ℓ (word E ((List.ofFn fun i => g (π i)).map τ) u) := by sorry
