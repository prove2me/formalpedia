-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_beta_sq
-- name    : CompanionTheory.D.LK.beta_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:17.359776+00:00
-- url     : https://prove2.me/theorems/33d2027e-d4d9-4b45-b668-2ab5f6d9cc98
-- title:
--   LK: beta sq
-- statement:
--   The LK construction uses the beta sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/KoszulDifferentialAnticommutator.lean#L127-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/KoszulDifferentialAnticommutator.lean#L127-L186

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator
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
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {ε : Fin n → Bool}
variable {R : Type} [Ring R] [Algebra ℂ R] (E : Fin n → Fin n → R) (an cr : Pos n → R)

theorem CompanionTheory.D.LK.beta_sq (haa : ∀ i j, an i * an j + an j * an i = 0) (hcc : ∀ i j, cr i * cr j + cr j * cr i = 0)
    (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) * (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) = 0 := by sorry
