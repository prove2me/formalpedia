-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_covariant_commutes_signed_column_sum
-- name    : Formalism.FourierDecayAlt.P.ScalarCastIdentities.covariant_commutes_signed_column_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:12:54.868801+00:00
-- url     : https://prove2.me/theorems/2032dea9-cdef-41a4-b1a2-0fda01c9faa9
-- title:
--   Scalar Cast Identities: covariant commutes signed column sum
-- statement:
--   The Scalar Cast Identities construction uses the covariant commutes signed column sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L306-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L306-L325

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

theorem Formalism.FourierDecayAlt.P.ScalarCastIdentities.covariant_commutes_signed_column_sum (hE : GlRel E) (η : Fin t → A) (hη : IsCov E η) (hηη : ∀ a b, η a * η b = η b * η a) (j : Fin t)
    (w : ℂ) : ∑ i, η i * mS E i j (w - 1) = ∑ i, mS E i j w * η i := by sorry
