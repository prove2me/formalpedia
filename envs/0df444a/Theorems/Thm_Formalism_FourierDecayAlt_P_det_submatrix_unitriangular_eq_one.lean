-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_det_submatrix_unitriangular_eq_one
-- name    : Formalism.FourierDecayAlt.P.det_submatrix_unitriangular_eq_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:38:47.914593+00:00
-- url     : https://prove2.me/theorems/31ab9365-97bb-4f8d-8b1d-f1a37f28bf04
-- title:
--   P: det submatrix unitriangular eq one
-- statement:
--   The P construction uses the det submatrix unitriangular eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetSubmatrixUnitriangularEqOne.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetSubmatrixUnitriangularEqOne.lean#L9-L17

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetSubmatrixUnitriangularEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 CardInsertEmbedding DeterminantReindex

theorem Formalism.FourierDecayAlt.P.det_submatrix_unitriangular_eq_one {m k : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) (hu : u ∈ C2.UTset m) (e : Fin k → Fin m)
    (he : ∀ t, (e t).val = t.val) : (u.submatrix e e).det = 1 := by sorry
