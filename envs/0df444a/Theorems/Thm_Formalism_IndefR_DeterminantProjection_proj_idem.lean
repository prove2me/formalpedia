-- Prove2me | Theorems.Thm_Formalism_IndefR_DeterminantProjection_proj_idem
-- name    : Formalism.IndefR.DeterminantProjection.proj_idem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:03.80939+00:00
-- url     : https://prove2.me/theorems/1656bbaf-544b-4752-9e81-034ef29ec975
-- title:
--   Determinant Projection: proj idem
-- statement:
--   The Determinant Projection construction uses the proj idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L38-L46

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.DeterminantProjection
variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]

theorem Formalism.IndefR.DeterminantProjection.proj_idem (u r : n → A) (hru : r ⬝ᵥ u = 1) :
    (replicateCol Unit u * replicateRow Unit r) * (replicateCol Unit u * replicateRow Unit r) =
      replicateCol Unit u * replicateRow Unit r := by sorry
