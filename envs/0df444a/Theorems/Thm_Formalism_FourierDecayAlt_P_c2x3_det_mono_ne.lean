-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_det_mono_ne
-- name    : Formalism.FourierDecayAlt.P.c2x3_det_mono_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:36:39.224835+00:00
-- url     : https://prove2.me/theorems/e2910ddb-1e02-4787-bf46-e34c5952434f
-- title:
--   P: c2x3 det mono ne
-- statement:
--   The P construction uses the c2x3 det mono ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerAntidiagonalExact.lean#L73-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerAntidiagonalExact.lean#L73-L91

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
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
open C2x2

theorem Formalism.FourierDecayAlt.P.c2x3_det_mono_ne {m k : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (e f : Fin k → Fin m) (he : Function.Injective e) (hf : Function.Injective f)
    (hs : ∀ j, ∃ i, e i = w (f j)) : ((C2.monoP w d).submatrix e f).det ≠ 0 := by sorry
