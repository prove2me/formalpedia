-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_conj_mul_eq_mul_conj
-- name    : Formalism.FourierDecayAlt.P.conj_mul_eq_mul_conj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:38:37.18139+00:00
-- url     : https://prove2.me/theorems/efca0afe-f8b6-4d35-bb7f-484eaa78e1a2
-- title:
--   P: conj mul eq mul conj
-- statement:
--   The P construction uses the conj mul eq mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InverseSplitting.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InverseSplitting.lean#L137-L139

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

theorem Formalism.FourierDecayAlt.P.conj_mul_eq_mul_conj {m : ℕ} (P X Y : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) :
    P⁻¹ * (X * Y) * P = (P⁻¹ * X * P) * (P⁻¹ * Y * P) := by sorry
