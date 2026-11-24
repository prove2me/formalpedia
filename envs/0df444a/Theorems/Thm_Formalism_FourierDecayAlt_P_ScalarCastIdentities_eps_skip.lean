-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_eps_skip
-- name    : Formalism.FourierDecayAlt.P.ScalarCastIdentities.eps_skip
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:06.181838+00:00
-- url     : https://prove2.me/theorems/a5c9c5d4-62f4-4c50-8dff-b76576b5db24
-- title:
--   Scalar Cast Identities: eps skip
-- statement:
--   The Scalar Cast Identities construction uses the eps skip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L341-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L341-L350

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScalarCastIdentities
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)

theorem Formalism.FourierDecayAlt.P.ScalarCastIdentities.eps_skip (t : ℕ) (q : Fin (t + 1)) (k : Fin t) :
    ((eps (skip1 q k) q : ℤ) : ℂ) * (-1 : ℂ) ^ ((skip1 q k : Fin (t + 1)) : ℕ) = (-1 : ℂ) ^ (k : ℕ) := by sorry
