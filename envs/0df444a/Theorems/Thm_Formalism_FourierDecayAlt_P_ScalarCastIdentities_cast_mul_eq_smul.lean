-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_cast_mul_eq_smul
-- name    : Formalism.FourierDecayAlt.P.ScalarCastIdentities.cast_mul_eq_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:09:36.833627+00:00
-- url     : https://prove2.me/theorems/26b7a6f5-4019-46c8-afbc-6a0fe4dc32c7
-- title:
--   Scalar Cast Identities: cast mul eq smul
-- statement:
--   The Scalar Cast Identities construction uses the cast mul eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L100-L101

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

theorem Formalism.FourierDecayAlt.P.ScalarCastIdentities.cast_mul_eq_smul {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (a : A) : ((z : ℤ) : A) * a = ((z : ℤ) : ℂ) • a := by sorry
