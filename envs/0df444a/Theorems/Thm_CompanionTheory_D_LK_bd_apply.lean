-- Prove2me | Theorems.Thm_CompanionTheory_D_LK_bd_apply
-- name    : CompanionTheory.D.LK.bd_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:16:00.22117+00:00
-- url     : https://prove2.me/theorems/3589a562-7107-4be2-b351-3110e95bf1b3
-- title:
--   LK: bd apply
-- statement:
--   The LK construction uses the bd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean#L16-L24

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
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
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem CompanionTheory.D.LK.bd_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (x : Cn n V) (A : Finset (Pos n)) :
    bd ε E x A = (∑ i : Pos n, if cpt ε i then E i.1.1 i.1.2 (ann i x A) else 0) +
      ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n, if Tri ε i j k then cre k (ann j (ann i x)) A else 0 := by sorry
