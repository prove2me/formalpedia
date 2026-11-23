-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_deg_pderiv
-- name    : CompanionTheory.D.LK.deg_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:44.105079+00:00
-- url     : https://prove2.me/theorems/74e6ad73-b53e-4c5d-a442-cfde04bb4ddf
-- title:
--   LK: deg pderiv
-- statement:
--   The LK construction uses the deg pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/GeneralizedVermaModulePolynomial.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/GeneralizedVermaModulePolynomial.lean#L15-L33

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_GeneralizedVermaModulePolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MvPolynomial
open scoped TensorProduct
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL GlobalTheory.CompanionTheory.DSVerma GlobalTheory.CompanionTheory.DSCover
open CompanionTheory.D.DSIC (KRel NC)

theorem CompanionTheory.D.LK.deg_pderiv {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (k : ℕ) (h : f.totalDegree ≤ k + 1) :
    (pderiv i f).totalDegree ≤ k := by sorry
