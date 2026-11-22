-- Prove2me | Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_tQ_eq
-- name    : Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.tQ_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:07.788984+00:00
-- url     : https://prove2.me/theorems/d139da2e-c5fa-4c7f-af3d-8ddaa89e72c3
-- title:
--   Pgsn2pfrla: t Q eq
-- statement:
--   The Pgsn2pfrla construction uses the t Q eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L124-L131

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

theorem Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.tQ_eq (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    (trace ℂ H (frQ c B)).re = ∑ i, c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by sorry
