-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_ann_mem
-- name    : CompanionTheory.D.LK.ann_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:17.152051+00:00
-- url     : https://prove2.me/theorems/54c53916-deba-4636-8752-995edb8563b6
-- title:
--   LK: ann mem
-- statement:
--   The LK construction uses the ann mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreAnnApply.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/CreAnnApply.lean#L16-L20

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreAnnApply
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_euler_filt
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_homotopy_ring
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_mem_filt_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open GlobalTheory.CompanionTheory.DSICKoszul (homotopy_ring filt mem_filt_succ euler_filt)
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem CompanionTheory.D.LK.ann_mem {Q : Submodule ℂ Z} {x : Cn n Z} (h : ∀ A, x A ∈ Q) (i : Pos n) (A : Finset (Pos n)) :
    ann i x A ∈ Q := by sorry
