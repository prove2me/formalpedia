-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_basis_iff_core
-- name    : Formalism.FourierDecayAlt.P.ScalarCastIdentities.basis_iff_core
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:09:14.531181+00:00
-- url     : https://prove2.me/theorems/2d4f4966-1ea0-49b5-9c5b-62a4bafb8a66
-- title:
--   Scalar Cast Identities: basis iff core
-- statement:
--   The Scalar Cast Identities construction uses the basis iff core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L227-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L227-L232

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

theorem Formalism.FourierDecayAlt.P.ScalarCastIdentities.basis_iff_core (y η : Fin t → A) (u : ℂ) (p q : Fin t) :
    (qdet E (u + 1) * ch2 E (u - 1) y (Pi.single p 1) η (Pi.single q 1) +
          chY E (u + 1) y (Pi.single q 1) * chX E (u - 1) (Pi.single p 1) η =
        chYY E u y η * chatA E u (Pi.single p 1) (Pi.single q 1)) ↔ Core E y η u p q := by sorry
