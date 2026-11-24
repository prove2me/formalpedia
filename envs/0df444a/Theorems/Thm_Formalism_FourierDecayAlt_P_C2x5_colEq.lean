-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_colEq
-- name    : Formalism.FourierDecayAlt.P.C2x5.colEq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:32:24.391804+00:00
-- url     : https://prove2.me/theorems/730fbe01-4e38-48fb-91ab-30ab196cd32a
-- title:
--   C2x5: col Eq
-- statement:
--   The C2x5 construction uses the col Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFlagVector.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFlagVector.lean#L74-L82

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x5
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x5.colEq {z : Fin (2 * r + k + 1) → ℂ} {s : B.Mat k r} {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (h : s * Fm k r z = Fm k r z * U) (b : Fin (r + 1)) :
    s *ᵥ fvec k r z b = ∑ c, U c b • fvec k r z c := by sorry
