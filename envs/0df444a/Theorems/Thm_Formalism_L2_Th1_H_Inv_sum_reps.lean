-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_Inv_sum_reps
-- name    : Formalism.L2.Th1.H.Inv.sum_reps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:29.369737+00:00
-- url     : https://prove2.me/theorems/e86efdcc-70ad-42a1-80bd-b9560b83a12a
-- title:
--   Inv: sum reps
-- statement:
--   The Inv construction uses the sum reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L41-L49

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.Inv
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.L2.Th1.H.Inv.sum_reps {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) (g : V → ℂ)
    (hg : ∀ y ∈ S, y ∉ Λ₁ → g y = 0) : ∃ y₀ ∈ S, y₀ ∈ Λ₁ ∧ ∑ y ∈ S, g y = g y₀ := by sorry
