-- Prove2me | Theorems.Thm_Formalism_IndefR_EigenDecomposition_exists_onb_of_commuting
-- name    : Formalism.IndefR.EigenDecomposition.exists_onb_of_commuting
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:12.684722+00:00
-- url     : https://prove2.me/theorems/54f80ea1-c45e-4de9-b9ef-155d2ee26087
-- title:
--   Eigen Decomposition: exists onb of commuting
-- statement:
--   The Eigen Decomposition construction uses the exists onb of commuting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/EigenDecomposition.lean#L45-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/EigenDecomposition.lean#L45-L124

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

theorem Formalism.IndefR.EigenDecomposition.exists_onb_of_commuting (A : Set (H →ₗ[ℂ] H))
    (hcomm : ∀ S ∈ A, ∀ T ∈ A, Commute S T)
    (hadj : ∀ T ∈ A, LinearMap.adjoint T ∈ A) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H), ∀ k, ∀ T ∈ A, ∃ μ : ℂ, T (b k) = μ • b k := by sorry
