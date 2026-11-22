-- Prove2me | Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_W_upper
-- name    : Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.W_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:59.827183+00:00
-- url     : https://prove2.me/theorems/f4e919d6-b0dd-4d7f-bbdb-31310d2b822b
-- title:
--   Pgsn2pfrla: W upper
-- statement:
--   The Pgsn2pfrla construction uses the W upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L164-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L164-L184

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
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.W_upper (B : V →ₗ[ℂ] H) (N : Submodule ℂ V) {κ : Type*} [Fintype κ] {g : κ → H}
    (hg : Orthonormal ℂ g) (hperp : ∀ l, ∀ n ∈ N, ⟪B n, g l⟫_ℂ = 0) :
    ∑ l, ‖adjoint B (g l)‖ ^ 2 ≤ ∑ m, ‖B ((stdOrthonormalBasis ℂ Nᗮ m : V))‖ ^ 2 := by sorry
