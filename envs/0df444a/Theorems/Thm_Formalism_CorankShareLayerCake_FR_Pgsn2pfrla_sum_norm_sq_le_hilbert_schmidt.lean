-- Prove2me | Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_sum_norm_sq_le_hilbert_schmidt
-- name    : Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.sum_norm_sq_le_hilbert_schmidt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:43.274929+00:00
-- url     : https://prove2.me/theorems/a1862e24-6801-4303-b45a-1b97f0af5f6b
-- title:
--   Pgsn2pfrla: sum norm sq le hilbert schmidt
-- statement:
--   The Pgsn2pfrla construction uses the sum norm sq le hilbert schmidt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L57-L67

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

theorem Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.sum_norm_sq_le_hilbert_schmidt {κ : Type*} [Fintype κ] (A : E →ₗ[ℂ] F) {g : κ → E} (hg : Orthonormal ℂ g) :
    ∑ l, ‖A (g l)‖ ^ 2 ≤ hs2 A := by sorry
