-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_negperp_gen
-- name    : Formalism.HermitianLatticeCounting.P.negperp_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:19.81352+00:00
-- url     : https://prove2.me/theorems/dc0a591b-4b3b-407a-a393-8b3299ee5780
-- title:
--   P: negperp gen
-- statement:
--   The P construction uses the negperp gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L1204-L1251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L1204-L1251

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

theorem Formalism.HermitianLatticeCounting.P.negperp_gen (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (hσ : ∀ x : K, σ (star x) = star (σ x))
    (herm : ∀ x y : U, star (h x y) = h y x) (A N : Submodule K U)
    (hN : ∀ n ∈ N, ∀ u ∈ A, h n u = 0) (z₀ : U) (_hz₀ : z₀ ∈ A)
    (pos : ∀ w ∈ A, h w z₀ = 0 → w ∉ N → 0 < (σ (h w w)).re)
    (z : U) (hz : z ∈ A) (hzn : (σ (h z z)).re < 0) (w : U) (hw : w ∈ A) (hwz : h w z = 0)
    (hwN : w ∉ N) : 0 < (σ (h w w)).re := by sorry
