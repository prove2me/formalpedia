-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_asym_sum
-- name    : Formalism.FourierDecayAlt.P.ScalarCastIdentities.asym_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:29:51.11229+00:00
-- url     : https://prove2.me/theorems/29975e6a-1e20-47d2-bf8b-00d9349a6330
-- title:
--   Scalar Cast Identities: asym sum
-- statement:
--   The Scalar Cast Identities construction uses the asym sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L69-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L69-L90

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

theorem Formalism.FourierDecayAlt.P.ScalarCastIdentities.asym_sum {B : Type*} [AddCommGroup B] {t : ℕ} (T : Fin t → Fin t → Fin t → Fin t → B) :
    ∑ i, ∑ i', (if i < i' then T i i' i i' - T i' i i i' else 0) =
      ∑ a, ∑ b, if a = b then 0 else eps a b • T a b (min a b) (max a b) := by sorry
