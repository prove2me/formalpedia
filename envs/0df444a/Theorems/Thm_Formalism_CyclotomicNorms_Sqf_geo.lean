-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_Sqf_geo
-- name    : Formalism.CyclotomicNorms.Sqf.geo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:39.690056+00:00
-- url     : https://prove2.me/theorems/95d05ff1-fa45-4adb-bf3b-4b6d3d1a5e01
-- title:
--   Sqf: geo
-- statement:
--   The Sqf construction uses the geo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L75-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L75-L90

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.Sqf
variable {K : Type} [Field K]

theorem Formalism.CyclotomicNorms.Sqf.geo (q : ℕ) (hq : 2 ≤ q) (N : ℕ) :
    ∀ k, k < N → (∑ d ∈ Icc 1 k, q ^ (N - d)) + 2 * q ^ (N - 1 - k) ≤ 2 * q ^ (N - 1) := by sorry
