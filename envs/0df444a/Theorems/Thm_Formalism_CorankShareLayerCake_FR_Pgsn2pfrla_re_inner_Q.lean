-- Prove2me | Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_re_inner_Q
-- name    : Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.re_inner_Q
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:09.930346+00:00
-- url     : https://prove2.me/theorems/e0dfb105-ba0d-429b-8601-bd86e00c8576
-- title:
--   Pgsn2pfrla: re inner Q
-- statement:
--   The Pgsn2pfrla construction uses the re inner Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L110-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L110-L115

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

theorem Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.re_inner_Q (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (x : H) :
    (⟪x, frQ c B x⟫_ℂ).re = ∑ i, c i * ‖adjoint (B i) x‖ ^ 2 := by sorry
