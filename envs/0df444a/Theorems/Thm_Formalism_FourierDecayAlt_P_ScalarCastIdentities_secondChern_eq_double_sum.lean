-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_secondChern_eq_double_sum
-- name    : Formalism.FourierDecayAlt.P.ScalarCastIdentities.secondChern_eq_double_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:09:38.253532+00:00
-- url     : https://prove2.me/theorems/d9c51161-d061-40f3-96ae-d04d07e1f47d
-- title:
--   Scalar Cast Identities: second Chern eq double sum
-- statement:
--   The Scalar Cast Identities construction uses the second Chern eq double sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L146-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L146-L207

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

theorem Formalism.FourierDecayAlt.P.ScalarCastIdentities.secondChern_eq_double_sum (w : ℂ) (y : Fin t → A) (x : Fin t → ℂ) (η : Fin t → A) (ξ : Fin t → ℂ) :
    ch2 E w y x η ξ = ∑ q, ∑ p, (ξ q * x p) • ∑ a, ∑ c, η a * y c * nS E a q c p w := by sorry
