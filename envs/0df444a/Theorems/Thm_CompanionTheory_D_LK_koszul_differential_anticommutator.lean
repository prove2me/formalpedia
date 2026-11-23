-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_koszul_differential_anticommutator
-- name    : CompanionTheory.D.LK.koszul_differential_anticommutator
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:48.997874+00:00
-- url     : https://prove2.me/theorems/5f9bc450-d859-48a0-b337-6836a606ea38
-- title:
--   LK: koszul differential anticommutator
-- statement:
--   The LK construction uses the koszul differential anticommutator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/KoszulDifferentialAnticommutator.lean#L96-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/KoszulDifferentialAnticommutator.lean#L96-L125

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

theorem CompanionTheory.D.LK.koszul_differential_anticommutator (h1 : ∀ a b i, Commute (E a b) (an i)) (h2 : ∀ a b i, Commute (E a b) (cr i))
    (haa : ∀ i j, an i * an j + an j * an i = 0) (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) * (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) +
      (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) * (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) =
      -∑ i, ∑ j, ∑ k, tc ε i j k • (E k.1.1 k.1.2 * (an i * an j)) := by sorry
