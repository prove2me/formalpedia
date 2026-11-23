-- Prove2me | Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_trace_frame_sq_eq_sum
-- name    : Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.trace_frame_sq_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:50.527835+00:00
-- url     : https://prove2.me/theorems/6dcfa80c-09a5-4e0e-b8ac-56c478e7d2a3
-- title:
--   Pgsn2pfrla: trace frame sq eq sum
-- statement:
--   The Pgsn2pfrla construction uses the trace frame sq eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L133-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L133-L140

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CorankShareLayerCake Formalism.CorankShareLayerCake.FR
open Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
open Finset Module LinearMap
open scoped InnerProductSpace
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.trace_frame_sq_eq_sum (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    (trace ℂ H (frQ c B ∘ₗ frQ c B)).re = ∑ n, ‖frQ c B (stdOrthonormalBasis ℂ H n)‖ ^ 2 := by sorry
