-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_alt_bound
-- name    : Formalism.LatticeIndexTer.alt_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:20.333863+00:00
-- url     : https://prove2.me/theorems/54cc8e4c-72a3-4cf2-ae68-98d0b2bb038e
-- title:
--   Lattice Index Ter: alt bound
-- statement:
--   The Lattice Index Ter construction uses the alt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SumInterlacedBoundFails.lean#L43-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SumInterlacedBoundFails.lean#L43-L63

import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Finset

theorem Formalism.LatticeIndexTer.alt_bound {α : Type*} [Preorder α] (f : α → ℝ) (hf : Monotone f) :
    ∀ (k : ℕ) (a : Fin (k + 1) → α) (b : Fin k → α),
      (∀ i : Fin k, b i ≤ a i.castSucc ∧ a i.succ ≤ b i) →
      f (a (Fin.last k)) ≤ (∑ i, f (a i)) - ∑ i, f (b i) ∧
      (∑ i, f (a i)) - ∑ i, f (b i) ≤ f (a 0) := by sorry
