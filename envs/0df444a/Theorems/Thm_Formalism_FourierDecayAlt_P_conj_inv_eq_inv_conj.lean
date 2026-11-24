-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_conj_inv_eq_inv_conj
-- name    : Formalism.FourierDecayAlt.P.conj_inv_eq_inv_conj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:39:00.359831+00:00
-- url     : https://prove2.me/theorems/2dfde013-2f99-42ae-b9b7-290d04f93312
-- title:
--   P: conj inv eq inv conj
-- statement:
--   The P construction uses the conj inv eq inv conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InverseSplitting.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InverseSplitting.lean#L141-L143

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InverseSplitting
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
open C2x2 InverseSplitting

theorem Formalism.FourierDecayAlt.P.conj_inv_eq_inv_conj {m : ℕ} (P X : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) :
    (P⁻¹ * X * P)⁻¹ = P⁻¹ * X⁻¹ * P := by sorry
