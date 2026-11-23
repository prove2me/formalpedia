-- Prove2me | Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_hilbert_schmidt_sub_scalar
-- name    : Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.hilbert_schmidt_sub_scalar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:41.970519+00:00
-- url     : https://prove2.me/theorems/6b849fb5-cd64-4894-be62-5d9724a53c1b
-- title:
--   Pgsn2pfrla: hilbert schmidt sub scalar
-- statement:
--   The Pgsn2pfrla construction uses the hilbert schmidt sub scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L142-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L142-L156

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

theorem Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.hilbert_schmidt_sub_scalar (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (lam : ℝ) :
    hs2 (frQ c B - (lam : ℂ) • LinearMap.id) =
      (trace ℂ H (frQ c B ∘ₗ frQ c B)).re - 2 * lam * (trace ℂ H (frQ c B)).re
        + lam ^ 2 * finrank ℂ H := by sorry
