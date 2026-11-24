-- Prove2me | Theorems.Thm_Formalism_IndefR_EigenDecomposition_exists_onb_of_parts_set
-- name    : Formalism.IndefR.EigenDecomposition.exists_onb_of_parts_set
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:02.854541+00:00
-- url     : https://prove2.me/theorems/46f4bf1b-fa22-45b2-9844-0a5f5958e926
-- title:
--   Eigen Decomposition: exists onb of parts set
-- statement:
--   The Eigen Decomposition construction uses the exists onb of parts set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/EigenDecomposition.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/EigenDecomposition.lean#L24-L33

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_EigenDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Formalism Formalism.IndefR Formalism.IndefR.EigenDecomposition
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem Formalism.IndefR.EigenDecomposition.exists_onb_of_parts_set {L : Type*} (S : Set L) (hS : S.Finite) (P : L → Submodule ℂ H)
    (horth : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → P c ⟂ P d) (htop : ⨆ c ∈ S, P c = ⊤) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H) (lab : Fin n → L),
      (∀ k, lab k ∈ S) ∧ ∀ k, b k ∈ P (lab k) := by sorry
