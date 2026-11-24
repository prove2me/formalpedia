-- Prove2me | Theorems.Thm_Formalism_IndefR_EigenDecomposition_exists_onb_of_parts
-- name    : Formalism.IndefR.EigenDecomposition.exists_onb_of_parts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:52.018537+00:00
-- url     : https://prove2.me/theorems/0328672d-a6f4-4607-b078-8f33b13e01ba
-- title:
--   Eigen Decomposition: exists onb of parts
-- statement:
--   The Eigen Decomposition construction uses the exists onb of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/EigenDecomposition.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/EigenDecomposition.lean#L9-L22

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

theorem Formalism.IndefR.EigenDecomposition.exists_onb_of_parts {I : Type*} [Finite I] (P : I → Submodule ℂ H)
    (horth : ∀ i j, i ≠ j → P i ⟂ P j) (htop : ⨆ i, P i = ⊤) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H) (lab : Fin n → I), ∀ k, b k ∈ P (lab k) := by sorry
