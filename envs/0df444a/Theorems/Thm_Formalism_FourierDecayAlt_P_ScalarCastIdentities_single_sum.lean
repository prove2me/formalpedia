-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_single_sum
-- name    : Formalism.FourierDecayAlt.P.ScalarCastIdentities.single_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:09:45.373866+00:00
-- url     : https://prove2.me/theorems/a1e858c5-c3db-4d89-86e6-1a3b1862686c
-- title:
--   Scalar Cast Identities: single sum
-- statement:
--   The Scalar Cast Identities construction uses the single sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L220-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L220-L221

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
variable {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)

theorem Formalism.FourierDecayAlt.P.ScalarCastIdentities.single_sum (q : Fin t) (F : Fin t → A) : ∑ q', (Pi.single q (1 : ℂ) : Fin t → ℂ) q' • F q' = F q := by sorry
