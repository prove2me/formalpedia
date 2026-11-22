-- Prove2me | Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_hilbert_schmidt_nonneg_alt
-- name    : Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.hilbert_schmidt_nonneg_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:13:26.572382+00:00
-- url     : https://prove2.me/theorems/bbb7ae3f-3d07-40e0-9a33-c1210908307d
-- title:
--   Pgsn2pfrla: hilbert schmidt nonneg alt
-- statement:
--   The Pgsn2pfrla construction uses the hilbert schmidt nonneg alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L53-L55

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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

theorem Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.hilbert_schmidt_nonneg_alt (A : E →ₗ[ℂ] F) : 0 ≤ hs2 A := by sorry
