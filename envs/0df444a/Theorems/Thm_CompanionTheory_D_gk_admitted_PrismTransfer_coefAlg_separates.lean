-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_coefAlg_separates
-- name    : CompanionTheory.D.gk.admitted.PrismTransfer.coefAlg_separates
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:51.745018+00:00
-- url     : https://prove2.me/theorems/fa7e5edd-33c1-44be-a4ad-ed08c4c737ed
-- title:
--   Prism Transfer: coef Alg separates
-- statement:
--   The Prism Transfer construction uses the coef Alg separates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L146-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L146-L157

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

theorem CompanionTheory.D.gk.admitted.PrismTransfer.coefAlg_separates (h : IsGood st S ρ) (hi : Function.Injective ρ) (C : Set G) :
    (coefAlg st S C).SeparatesPoints := by sorry
