-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_reverseCS_gen
-- name    : Formalism.HermitianLatticeCounting.P.reverseCS_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:51.781671+00:00
-- url     : https://prove2.me/theorems/12ec4196-a36f-407e-8285-759db60634c6
-- title:
--   P: reverse CS gen
-- statement:
--   The P construction uses the reverse CS gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L1253-L1317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L1253-L1317

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]

theorem Formalism.HermitianLatticeCounting.P.reverseCS_gen (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (hσ : ∀ x : K, σ (star x) = star (σ x))
    (herm : ∀ x y : U, star (h x y) = h y x) (A N : Submodule K U)
    (hN : ∀ n ∈ N, ∀ u ∈ A, h n u = 0) (z₀ : U) (hz₀ : z₀ ∈ A)
    (pos : ∀ w ∈ A, h w z₀ = 0 → w ∉ N → 0 < (σ (h w w)).re)
    (z : U) (hz : z ∈ A) (hzn : (σ (h z z)).re < 0) (z' : U) (hz' : z' ∈ A) :
    (σ (h z z)).re * (σ (h z' z')).re ≤ Complex.normSq (σ (h z z')) ∧
      (h z z * h z' z' = h z z' * star (h z z') → ∃ c : K, z' - c • z ∈ N) := by sorry
