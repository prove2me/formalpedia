-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ViF_alt
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.ViF_alt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:32:10.60274+00:00
-- url     : https://prove2.me/theorems/74bdfd12-0c95-5ea3-9823-25f039c9fe41
-- title:
--   Sign Antidiagonal: Vi F alt
-- statement:
--   The Sign Antidiagonal construction uses the Vi F alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L62-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L62-L74

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianInsertionVectorOrthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.ViF_alt (l : Fin (2 * (m + 1) + k + 1)) : ViF m i Vc l = 0 ∨ ViF m i Vc (WeylGroupFacts.tau k (m + 1) l) = 0 := by sorry
