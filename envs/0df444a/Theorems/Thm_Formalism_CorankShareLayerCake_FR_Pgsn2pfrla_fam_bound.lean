-- Prove2me | Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_fam_bound
-- name    : Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.fam_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:09.207808+00:00
-- url     : https://prove2.me/theorems/56fcb899-cc3e-45df-bf13-17da2aaf7546
-- title:
--   Pgsn2pfrla: fam bound
-- statement:
--   The Pgsn2pfrla construction uses the fam bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L87-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/SumNormSqLeHilbertSchmidt.lean#L87-L101

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

theorem Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.fam_bound (c : ℝ) (B : E →ₗ[ℂ] F) {κ : Type*} [Fintype κ] {g : κ → E}
    (hg : Orthonormal ℂ g) :
    |c * ∑ l, ‖B (g l)‖ ^ 2 - Fintype.card κ|
      ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (hs2 (frK c B - LinearMap.id)) := by sorry
